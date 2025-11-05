// ESP32-S3 STL FileHub — single .ino, UTF-8 safe, special-char filenames fixed
// Target: ESP32-S3 Dev Module (SuperMini), 4MB Flash, NO PSRAM
// Partition: Default or "Huge APP (3MB No OTA)"
//
// SD (SPI) pins: CS=5, MOSI=11, MISO=13, SCK=9
// SD Folders: /stl     (STL files)
//             /thumbs  (PNG thumbnails)
//
// Notes:
//  • Thumbnails are 160x120 (RGBA + uint16 Z), ~115 KB buffers total.
//  • ASCII→Binary STL conversion is streaming (no pre-count). Triangle count patched at end.
//  • Self-hosted preview (no CDN): /stlview.js is served by the ESP32.
//  • Filenames with spaces, +, and UTF-8 accents fully supported in list/preview/download/delete.
//  • '+' is encoded as %2B and remains '+' after decoding (no form-urlencoded '+'→space conversion).
//
// ───────────────────────────────────────────────────────────────────────────────

#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <SPI.h>
#include <SD.h>
#include <FS.h>
#include <vector>
#include <algorithm>
#include <ctype.h>
#include <math.h>
#include <string.h>
#include <stdio.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

// ===== Pins & Wi-Fi =====
#define SD_CS   5
#define SD_SCK  9
#define SD_MOSI 11
#define SD_MISO 13

const char* WIFI_SSID = "Platform 9 3/4";
const char* WIFI_PASS = "Screamforpassword123";
const bool  ENABLE_AP_FALLBACK = true;
const char* AP_SSID   = "S3_FileHub";
const char* AP_PASS   = "12345678";

// Optionally wipe thumbs on boot (off by default)
static const bool REBUILD_THUMBS_ON_BOOT = false;

// ===== Paths =====
static const char* STL_DIR = "/stl";
static const char* TH_DIR  = "/thumbs";

WebServer server(80);

// ===== Types =====
struct Item {
  String name, path;
  bool isDir;
  uint64_t size;
  uint32_t pseudoTime;
};

struct Vec3 { float x, y, z; };

// ===== Thumbnail image buffers (160x120), depth as uint16 =====
static const int TH_W = 160, TH_H = 120;

struct ImgBuf {
  uint8_t  rgba[TH_W * TH_H * 4];
  uint16_t zbuf[TH_W * TH_H];

  static inline uint16_t dz(float z){
    float t = (z + 2.0f) * 0.25f; // [-2..+2] -> [0..1]
    if (t < 0) t = 0;
    if (t > 1) t = 1;
    return (uint16_t)(t * 65535.0f + 0.5f);
  }
  void clear(uint8_t r = 235, uint8_t g = 238, uint8_t b = 245, uint8_t a = 255){
    for (int i = 0; i < TH_W * TH_H; i++){
      rgba[i*4 + 0] = r; rgba[i*4 + 1] = g; rgba[i*4 + 2] = b; rgba[i*4 + 3] = a;
      zbuf[i] = 0xFFFF;
    }
  }
  inline void setRGBA(int x, int y, uint8_t r, uint8_t g, uint8_t b, uint8_t a, float z){
    if ((unsigned)x >= TH_W || (unsigned)y >= TH_H) return;
    int idx = y * TH_W + x;
    uint16_t zz = dz(z);
    if (zz < zbuf[idx]){
      zbuf[idx] = zz;
      rgba[idx*4 + 0] = r; rgba[idx*4 + 1] = g; rgba[idx*4 + 2] = b; rgba[idx*4 + 3] = a;
    }
  }
};

static ImgBuf g_img;

// ===== PNG CRC + Writer =====
struct PNGCrc{
  uint32_t crc=0xFFFFFFFFu;
  static inline uint32_t upd(uint32_t c,uint8_t b){ c^=b; for(int i=0;i<8;i++) c=(c&1)?(0xEDB88320u^(c>>1)):(c>>1); return c; }
  void feedByte(uint8_t b){ crc=upd(crc,b); }
  void feed(const uint8_t* p,size_t n){ for(size_t i=0;i<n;i++) feedByte(p[i]); }
  uint32_t get(){ return ~crc; }
};
static inline bool writeU32(File& f,uint32_t v){ uint8_t b[4]={(uint8_t)(v>>24),(uint8_t)(v>>16),(uint8_t)(v>>8),(uint8_t)v}; return f.write(b,4)==4; }
static bool chunkBegin(File& f,const char* type,uint32_t len, PNGCrc& crc){
  if(!writeU32(f,len)) return false;
  if(f.write((const uint8_t*)type,4)!=4) return false;
  crc=PNGCrc(); crc.feed((const uint8_t*)type,4);
  return true;
}
static bool chunkData(File& f, PNGCrc& crc, const uint8_t* data, uint32_t n){
  if(n && f.write(data,n)!=n) return false;
  if(n) crc.feed(data,n);
  return true;
}
static bool chunkEnd(File& f, PNGCrc& crc){ return writeU32(f, crc.get()); }

static bool writePNGRGBA_stream(File& f,const uint8_t* img,uint32_t W,uint32_t H){
  static const uint8_t sig[8]={137,80,78,71,13,10,26,10};
  if(!f.write(sig,8)) return false;

  uint8_t IHDR[13];
  IHDR[0]=(W>>24)&255;IHDR[1]=(W>>16)&255;IHDR[2]=(W>>8)&255;IHDR[3]=W&255;
  IHDR[4]=(H>>24)&255;IHDR[5]=(H>>16)&255;IHDR[6]=(H>>8)&255;IHDR[7]=H&255;
  IHDR[8]=8;IHDR[9]=6;IHDR[10]=0;IHDR[11]=0;IHDR[12]=0;
  PNGCrc cIH; if(!chunkBegin(f,"IHDR",13,cIH)) return false;
  if(!chunkData(f,cIH,IHDR,13)) return false;
  if(!chunkEnd(f,cIH)) return false;

  const uint32_t row = 1 + 4*W;     // filter byte + RGBA row
  const uint32_t raw = H * row;
  const uint32_t max_rows = 65535u / row;
  uint32_t rows_remaining = H;
  const uint32_t blocks = (rows_remaining + max_rows - 1) / max_rows;
  const uint32_t zlen = 2 + blocks*5 + raw + 4;

  PNGCrc cID; if(!chunkBegin(f,"IDAT", zlen, cID)) return false;
  uint8_t zhdr[2]={0x78,0x01}; if(!chunkData(f,cID,zhdr,2)) return false;

  uint32_t s1=1,s2=0, rows_written=0;
  while(rows_remaining){
    uint32_t rb = rows_remaining; if(rb>max_rows) rb=max_rows;
    uint32_t LEN = rb * row; uint16_t L16=(uint16_t)LEN, NL16=~L16;
    uint8_t bh[5]; bh[0]=(rows_remaining==rb)?1:0; bh[1]=L16&0xFF; bh[2]=(L16>>8)&0xFF; bh[3]=NL16&0xFF; bh[4]=(NL16>>8)&0xFF;
    if(!chunkData(f,cID,bh,5)) return false;

    for(uint32_t r=0;r<rb;r++){
      uint8_t filter=0; if(!chunkData(f,cID,&filter,1)) return false;
      s1=(s1+filter)%65521; s2=(s2+s1)%65521;

      const uint8_t* line = img + (rows_written+r)*W*4;
      if(!chunkData(f,cID, line, W*4)) return false;
      for(uint32_t i=0;i<W*4;i++){ s1=(s1+line[i])%65521; s2=(s2+s1)%65521; }
    }
    rows_written += rb; rows_remaining -= rb;
  }

  uint32_t ad=(s2<<16)|s1; uint8_t ad4[4]={(uint8_t)(ad>>24),(uint8_t)(ad>>16),(uint8_t)(ad>>8),(uint8_t)ad};
  if(!chunkData(f,cID,ad4,4)) return false;
  if(!chunkEnd(f,cID)) return false;

  PNGCrc cIE; if(!chunkBegin(f,"IEND",0,cIE)) return false;
  if(!chunkEnd(f,cIE)) return false;
  return true;
}

// ===== Small HTML escaper (prevents markup breakage) =====
String htmlEscape(const String& s){
  String o; o.reserve(s.length()*2);
  for (size_t i=0;i<s.length();++i){
    char c=s[i];
    if(c=='&') o += F("&amp;");
    else if(c=='<') o += F("&lt;");
    else if(c=='>') o += F("&gt;");
    else if(c=='"') o += F("&quot;");
    else o += c;
  }
  return o;
}

// ===== Utils =====
int ciCmp(const String& A, const String& B){
  size_t na=A.length(), nb=B.length(), n = (na<nb?na:nb);
  for(size_t i=0;i<n;i++){
    char a=tolower((unsigned char)A[i]);
    char b=tolower((unsigned char)B[i]);
    if(a<b) return -1;
    if(a>b) return 1;
  }
  if(na<nb) return -1;
  if(na>nb) return 1;
  return 0;
}
static inline float fmin3(float a,float b,float c){return min(a,min(b,c));}
static inline float fmax3(float a,float b,float c){return max(a,max(b,c));}
static inline float edgeFunc(float x0,float y0,float x1,float y1,float x,float y){ return (x-x0)*(y1-y0)-(y-y0)*(x1-x0); }

String ensureSlash(const String& n){ return (n.length() && n[0]=='/')? n : ("/"+n); }
String joinPath(const String& a,const String& b){ if(a.endsWith("/")) return a + b; return a + "/" + b; }
bool hasSTLExt(const String& n){ String lo=n; lo.toLowerCase(); return lo.endsWith(".stl"); }
String baseNameNoExt(const String& p){ int s=p.lastIndexOf('/'); int st=(s>=0)?s+1:0; int d=p.lastIndexOf('.'); if(d<st) d=p.length(); return p.substring(st,d); }

String humanSize(uint64_t b){
  char out[40];
  if(b<1024ULL) sprintf(out,"%llu B",(unsigned long long)b);
  else if(b<1048576ULL) sprintf(out,"%.2f KB", b/1024.0);
  else if(b<1073741824ULL) sprintf(out,"%.2f MB", b/1048576.0);
  else sprintf(out,"%.2f GB", b/1073741824.0);
  return String(out);
}

// RFC 3986 encode for query values; keep '/' so paths survive in the value.
// Any UTF-8 bytes (>127) are percent-encoded byte-wise. '+' is encoded as %2B.
String urlEncode(const String& s){
  const char* hex="0123456789ABCDEF";
  String out; out.reserve(s.length()*3);
  for(size_t i=0;i<s.length();i++){
    unsigned char c=(unsigned char)s[i];
    if((c>='A'&&c<='Z')||(c>='a'&&c<='z')||(c>='0'&&c<='9')||c=='-'||c=='_'||c=='.'||c=='~'||c=='/'){
      out += (char)c;
    }else{
      out += '%'; out += hex[(c>>4)&0xF]; out += hex[c&0xF];
    }
  }
  return out;
}

// Percent-decoder for query values. DOES NOT convert '+' to space.
// This preserves literal '+' in filenames; '%2B' also becomes '+'.
String urlDecodeMin(const String& s){
  String out; out.reserve(s.length());
  for(size_t i=0;i<s.length();){
    char c=s[i];
    if(c=='%' && i+2<s.length()){
      auto h=[&](char ch)->int{ if(ch>='0'&&ch<='9')return ch-'0'; if(ch>='A'&&ch<='F')return ch-'A'+10; if(ch>='a'&&ch<='f')return ch-'a'+10; return -1; };
      int a=h(s[i+1]); int b=h(s[i+2]);
      if(a>=0&&b>=0){ out += char((a<<4)|b); i+=3; continue; }
    }
    // DO NOT treat '+' specially.
    out += c; i++;
  }
  return out;
}

// Sanitize directory path to make sure it is valid and always starts with "/stl"
String sanitizeDir(String dir) {
  if (!dir.length()) return String(STL_DIR);
  if (dir[0] != '/') dir = "/" + dir;
  // Prevent escaping to parent folders like "/../"
  dir.replace("..", "");
  // Force everything to stay inside /stl
  if (!dir.startsWith(STL_DIR)) {
    dir = String(STL_DIR);
  }
  // Strip trailing slash except for root /stl
  if (dir.length()>1 && dir.endsWith("/")) dir.remove(dir.length()-1);
  return dir;
}

// ===== CRC32 util for path hashing (thumb file naming) =====
static uint32_t crc32_upd(uint32_t c, uint8_t b){ c^=b; for(int i=0;i<8;i++) c=(c&1)?(0xEDB88320u^(c>>1)):(c>>1); return c; }
static uint32_t crc32_bytes(const uint8_t* p, size_t n){ uint32_t c=0xFFFFFFFFu; for(size_t i=0;i<n;i++) c=crc32_upd(c,p[i]); return ~c; }

// Canonical path used **only** for hashing to keep the CRC stable across lists/views.
String canonicalForHash(String p){
  if (!p.length() || p[0]!='/') p = "/" + p;
  while (p.indexOf("//")>=0) p.replace("//","/");
  if (hasSTLExt(p) && !p.startsWith(STL_DIR)) p = joinPath(String(STL_DIR), (p[0]=='/')? p.substring(1):p);
  return p;
}
static uint32_t crc32_str_canonical(const String& s){
  String canon = canonicalForHash(s);
  return crc32_bytes((const uint8_t*)canon.c_str(), canon.length());
}

// ===== Live progress for UI polling =====
static volatile bool g_busy=false; static volatile int g_prog=0;
static String g_task="", g_file="", g_statusLine="";
inline void setTask(const char* t){ g_task=t; }
inline void setProg(int p){ if(p<0)p=0; if(p>100)p=100; g_prog=p; }
inline void setStatus(const char* t, const String& f, int p){ setTask(t); g_file=f; setProg(p); g_busy=true; g_statusLine=String(t)+": "+f; }
inline void setStatusText(const String& s){ g_statusLine=s; }

// ===== Helper: keep HTTP responsive during heavy work =====
static inline void heartbeat(){
  server.handleClient(); // serve /qstate and others
  delay(0);              // yield to WiFi/RTOS
}

// ===== Thumb filename: sanitized + 8-hex CRC of canonical path =====
static String sanitizeForThumb(const String& s){
  String out; out.reserve(s.length());
  for(size_t i=0;i<s.length();++i){
    char c = s[i];
    if( (c>='a'&&c<='z') || (c>='A'&&c<='Z') || (c>='0'&&c<='9') || c=='_' || c=='-' ) out += c;
    else out += '_';
  }
  return out;
}
static String pngFor(const String& stlPath){
  String canon = canonicalForHash(stlPath);
  String base  = baseNameNoExt(canon);
  String san   = sanitizeForThumb(base);
  char hex[9]; uint32_t h = crc32_str_canonical(canon); sprintf(hex, "%08X", (unsigned)h);
  return String(TH_DIR) + "/" + san + "_" + hex + ".png";
}

// ===== Iso + raster (thumbnail) =====
static inline void isoRotate(const Vec3& in, Vec3& out){
  const float ay=45.0f*(float)M_PI/180.0f;
  const float ax=35.264f*(float)M_PI/180.0f;
  const float cy=cosf(ay), sy=sinf(ay);
  const float cx=cosf(ax), sx=sinf(ax);
  float xr=in.x*cy+in.z*sy;
  float zr=-in.x*sy+in.z*cy;
  float yr=in.y;
  out.x=xr; out.y=yr*cx-zr*sx; out.z=yr*sx+zr*cx;
}
static inline void drawTriRGBA(ImgBuf& img,
  float x0,float y0,float z0,float x1,float y1,float z1,float x2,float y2,float z2,
  uint8_t r,uint8_t g,uint8_t b,uint8_t a)
{
  float minx=floorf(fmin3(x0,x1,x2)), maxx=ceilf(fmax3(x0,x1,x2));
  float miny=floorf(fmin3(y0,y1,y2)), maxy=ceilf(fmax3(y0,y1,y2));
  if(maxx<0||maxy<0||minx>=TH_W||miny>=TH_H) return;
  int ix0=max(0,(int)minx), ix1=min(TH_W-1,(int)maxx);
  int iy0=max(0,(int)miny), iy1=min(TH_H-1,(int)maxy);
  float area=edgeFunc(x0,y0,x1,y1,x2,y2); if(area==0) return;
  float invA=1.0f/area;
  for(int y=iy0;y<=iy1;y++){
    for(int x=ix0;x<=ix1;x++){
      float w0=edgeFunc(x1,y1,x2,y2,x+0.5f,y+0.5f)*invA;
      float w1=edgeFunc(x2,y2,x0,y0,x+0.5f,y+0.5f)*invA;
      float w2=1.0f-w0-w1;
      if(w0>=0&&w1>=0&&w2>=0){
        float z=w0*z0+w1*z1+w2*z2;
        img.setRGBA(x,y,r,g,b,a,z);
      }
    }
  }
}
static void drawShadowEllipse(ImgBuf& img, float cx, float cy, float rx, float ry, uint8_t a){
  float z=1e29f;
  int xmin=max(0,(int)floorf(cx-rx)), xmax=min(TH_W-1,(int)ceilf(cx+rx));
  int ymin=max(0,(int)floorf(cy-ry)), ymax=min(TH_H-1,(int)ceilf(cy+ry));
  for(int y=ymin;y<=ymax;y++){
    for(int x=xmin;x<=xmax;x++){
      float nx=(x-cx)/rx, ny=(y-cy)/ry, d=nx*nx+ny*ny;
      if(d<=1.0f){ float t=1.0f-d; if(t<0)t=0; if(t>1)t=1; uint8_t al=(uint8_t)(a*t); img.setRGBA(x,y,0,0,0,al,z); }
    }
  }
}

// ===== Robust STL detection =====
static bool isLikelyAsciiSTL(File &f){
  if(!f) return false;
  size_t n = min<uint32_t>(512, f.size());
  std::vector<uint8_t> buf(n);
  f.seek(0);
  f.read(buf.data(), n);
  bool startsSolid = (n>=5 && memcmp(buf.data(),"solid",5)==0);
  int nonPrint=0;
  for(size_t i=0;i<n;i++){
    uint8_t c=buf[i];
    if(c==9||c==10||c==13) continue;
    if(c<32 || c>126) nonPrint++;
  }
  if(nonPrint>0 && !startsSolid) return false;
  if(startsSolid && nonPrint<10) return true;
  const char* p=(const char*)buf.data();
  return strstr(p,"facet")!=nullptr;
}

// ===== Binary STL bounds & render =====
static bool boundsBinary(File& f, Vec3& c, float& diag){
  if(!f) return false;
  if(f.size()<84) return false;
  f.seek(80); uint32_t tri; if(f.read((uint8_t*)&tri,4)!=4) return false;
  uint64_t expected=84ULL + (uint64_t)tri*50ULL;
  if(expected != (uint64_t)f.size()) return false;
  f.seek(84);
  Vec3 v0,v1,v2,n; float xmin=1e30f,xmax=-1e30f,ymin=1e30f,ymax=-1e30f,zmin=1e30f,zmax=-1e30f;
  for(uint32_t i=0;i<tri;i++){
    if(f.read((uint8_t*)&n,12)!=12) return false;
    if(f.read((uint8_t*)&v0,12)!=12) return false;
    if(f.read((uint8_t*)&v1,12)!=12) return false;
    if(f.read((uint8_t*)&v2,12)!=12) return false;
    f.seek(f.position()+2);
    xmin=min(xmin,fmin3(v0.x,v1.x,v2.x)); xmax=max(xmax,fmax3(v0.x,v1.x,v2.x));
    ymin=min(ymin,fmin3(v0.y,v1.y,v2.y)); ymax=max(ymax,fmax3(v0.y,v1.y,v2.y));
    zmin=min(zmin,fmin3(v0.z,v1.z,v2.z)); zmax=max(zmax,fmax3(v0.z,v1.z,v2.z));
    if((i & 0x3FF)==0){ heartbeat(); }
  }
  c.x=(xmin+xmax)*0.5f; c.y=(ymin+ymax)*0.5f; c.z=(zmin+zmax)*0.5f;
  diag=max(max(xmax-xmin,ymax-ymin),zmax-zmin); if(diag<=0) diag=1.0f;
  return true;
}
static bool renderBinary(File& f, ImgBuf& img, const Vec3& c, float diag){
  if(!f) return false;
  f.seek(80); uint32_t tri; if(f.read((uint8_t*)&tri,4)!=4) return false;
  f.seek(84);
  Vec3 v0,v1,v2,n;
  const float half = min(TH_W,TH_H) * 0.78f;
  const Vec3 L={0.577f,0.577f,0.577f};
  auto proj=[&](const Vec3& v,float& x2,float& y2,float& z2){
    Vec3 t{ (v.x-c.x)/diag, (v.y-c.y)/diag, (v.z-c.z)/diag }, r;
    isoRotate(t,r);
    x2=r.x*half + TH_W*0.5f; y2=-r.y*half + TH_H*0.5f; z2=r.z;
  };
  float pminx=1e9f,pmaxx=-1e9f,pminy=1e9f,pmaxy=-1e9f;

  // Live progress during raster
  const int startP = 60;      // start "Rendering" at 60%
  const int endP   = 85;      // finish rendering at ~85%
  setProg(startP);

  for(uint32_t i=0;i<tri;i++){
    if(f.read((uint8_t*)&n,12)!=12) return false;
    if(f.read((uint8_t*)&v0,12)!=12) return false;
    if(f.read((uint8_t*)&v1,12)!=12) return false;
    if(f.read((uint8_t*)&v2,12)!=12) return false;
    f.seek(f.position()+2);
    Vec3 rn; isoRotate(n, rn);
    float nl=sqrtf(rn.x*rn.x+rn.y*rn.y+rn.z*rn.z); if(nl>0){ rn.x/=nl; rn.y/=nl; rn.z/=nl; }
    float diffuse = max(0.0f, rn.x*L.x + rn.y*L.y + rn.z*L.z);
    Vec3 Vv={0.0f,0.0f,1.0f};
    Vec3 Hh={(L.x+Vv.x),(L.y+Vv.y),(L.z+Vv.z)};
    float hl=sqrtf(Hh.x*Hh.x+Hh.y*Hh.y+Hh.z*Hh.z); if(hl>0){ Hh.x/=hl; Hh.y/=hl; Hh.z/=hl; }
    float spec = powf(max(0.0f, rn.x*Hh.x + rn.y*Hh.y + rn.z*Hh.z), 42.0f);
    float rim  = powf(max(0.0f, 1.0f - fabsf(rn.z)), 1.5f);
    float shade = 0.10f + 0.88f*diffuse + 0.70f*spec + 0.22f*rim; if(shade>1.0f) shade=1.0f;
    float br=0.80f, bg=0.83f, bb2=0.90f;
    uint8_t rr=(uint8_t)max(0, min(255,(int)(255.0f*br*shade)));
    uint8_t gg=(uint8_t)max(0, min(255,(int)(255.0f*bg*shade)));
    uint8_t bb=(uint8_t)max(0, min(255,(int)(255.0f*bb2*shade)));
    float x0,y0,z0,x1,y1,z1,x2,y2,z2; proj(v0,x0,y0,z0); proj(v1,x1,y1,z1); proj(v2,x2,y2,z2);
    pminx=min(pminx, fmin3(x0,x1,x2)); pmaxx=max(pmaxx, fmax3(x0,x1,x2));
    pminy=min(pminy, fmin3(y0,y1,y2)); pmaxy=max(pmaxy, fmax3(y0,y1,y2));
    float area=(x1-x0)*(y2-y0)-(y1-y0)*(x2-x0); if(area<=0) continue;
    drawTriRGBA(img,x0,y0,z0,x1,y1,z1,x2,y2,z2, rr,gg,bb,255);

    if((i & 0x3FF)==0){
      int p = startP + (int)((uint64_t)i * (endP - startP) / (tri ? tri : 1));
      setProg(p);
      heartbeat();
    }
  }
  if(pmaxx>pminx && pmaxy>pminy){
    float cx=(pminx+pmaxx)*0.5f, cy=pmaxy+4.0f, rx=(pmaxx-pminx)*0.40f, ry=(pmaxx-pminx)*0.22f;
    drawShadowEllipse(g_img, cx, cy, rx, ry, 90);
  }
  setProg(endP);
  return true;
}

// ===== ASCII → Binary (streamed; header patched) =====
static bool convertAsciiToBinary_stream(const String& path){
  File in=SD.open(path, FILE_READ);
  if(!in) return false;

  if(in.size()>=84){
    in.seek(80); uint32_t tri; if(in.read((uint8_t*)&tri,4)==4){
      uint64_t exp=84ULL+(uint64_t)tri*50ULL;
      if((uint64_t)in.size()==exp){ in.close(); return true; }
    }
  }
  in.seek(0);
  if(!isLikelyAsciiSTL(in)){ in.close(); return true; }

  String tmp=path+".tmp";
  SD.remove(tmp);
  File out=SD.open(tmp, FILE_WRITE);
  if(!out){ in.close(); return false; }

  uint8_t hdr[80]; memset(hdr,0,sizeof(hdr));
  out.write(hdr,80);
  uint32_t triCount=0;
  out.write((uint8_t*)&triCount,4);

  in.seek(0);
  char lineBuf[256];
  Vec3 n={0,0,1}, v[3]; int vi=0;
  auto startsWith = [](const String& s, const char* p)->bool{
    int L=strlen(p); if((int)s.length()<L) return false;
    for(int i=0;i<L;i++) if(tolower((unsigned char)s[i])!=tolower((unsigned char)p[i])) return false;
    return true;
  };

  while(in.available()){
    size_t k = in.readBytesUntil('\n', lineBuf, sizeof(lineBuf)-1);
    lineBuf[k]=0;
    String line(lineBuf); line.trim();
    if(!line.length()) { heartbeat(); continue; }

    if(startsWith(line,"facet normal")){
      float nx=0,ny=0,nz=1;
      sscanf(line.c_str(),"facet normal %f %f %f",&nx,&ny,&nz);
      n={nx,ny,nz}; vi=0;
    }else if(startsWith(line,"vertex")){
      float x=0,y=0,z=0;
      sscanf(line.c_str(),"vertex %f %f %f",&x,&y,&z);
      v[vi++]={x,y,z};
      if(vi==3){
        out.write((uint8_t*)&n,12);
        out.write((uint8_t*)&v[0],12);
        out.write((uint8_t*)&v[1],12);
        out.write((uint8_t*)&v[2],12);
        uint16_t a=0; out.write((uint8_t*)&a,2);
        triCount++; vi=0;
      }
    }
    if((triCount & 0x7FF)==0) { heartbeat(); }
  }

  in.close();
  out.flush();
  out.seek(80);
  out.write((uint8_t*)&triCount,4);
  out.close();

  if(triCount==0){ SD.remove(tmp); return false; }

  SD.remove(path);
  if(!SD.rename(tmp.c_str(), path.c_str())){ SD.remove(tmp); return false; }
  return true;
}

// ===== Thumbnail generation =====
static volatile bool g_qbusy=false;
static bool generateThumbPNG(const char* stlPath,const char* pngPath){
  setStatus("Converting", stlPath, 5);
  if(!convertAsciiToBinary_stream(String(stlPath))){
    Serial.println("ASCII->BIN conversion failed"); g_busy=false; return false;
  }
  heartbeat();

  setStatus("Bounding", stlPath, 20);
  File f=SD.open(stlPath, FILE_READ); if(!f){ Serial.printf("open STL fail (%s)\n", stlPath); g_busy=false; return false; }
  Vec3 c; float diag; g_img.clear();
  if(!boundsBinary(f,c,diag)){ f.close(); Serial.println("⚠ Binary STL bounds failed"); g_busy=false; return false; }
  heartbeat();

  setStatus("Rendering", stlPath, 60);
  f.seek(0); bool ok=renderBinary(f,g_img,c,diag); f.close();
  if(!ok){ Serial.println("render fail"); g_busy=false; return false; }
  heartbeat();

  setStatus("Writing PNG", stlPath, 90);
  SD.remove(pngPath);
  File png=SD.open(pngPath, FILE_WRITE); if(!png){ Serial.printf("open PNG fail (%s)\n", stlPath); g_busy=false; return false; }
  bool wrote=writePNGRGBA_stream(png,g_img.rgba,TH_W,TH_H); png.close();

  setStatus("Done", stlPath, 100);
  delay(5);
  g_busy=false;
  return wrote;
}

// ===== Queue =====
static const int QMAX=128; static String qitems[QMAX]; static int qhead=0,qtail=0;
static bool qIsEmpty(){ return qhead==qtail; }
static bool qIsFull(){ return ((qhead+1)%QMAX)==qtail; }
static void qEnqueue(const String& p){
  if(!qIsFull()){
    String s=p;
    if(!s.startsWith(STL_DIR)) s=joinPath(String(STL_DIR), s[0]=='/'? s.substring(1):s);
    qitems[qhead]=s; qhead=(qhead+1)%QMAX;
  }
}
static String qDequeue(){ if(qIsEmpty()) return String(); String s=qitems[qtail]; qitems[qtail]=String(); qtail=(qtail+1)%QMAX; return s; }
static void ensureDir(const char* d){ if(!SD.exists(d)) SD.mkdir(d); }

static void scanDirAndQueueMissing(const String& dir){
  File r=SD.open(dir); if(!r||!r.isDirectory()) return;
  File f=r.openNextFile();
  while(f){
    String n=f.name();
    if(f.isDirectory()){
      if(n==String(TH_DIR) || n.startsWith(String(TH_DIR)+"/")) { f=r.openNextFile(); continue; }
      scanDirAndQueueMissing(n);
    } else if(hasSTLExt(n)){
      String png=pngFor(n);
      if(!SD.exists(png)){ Serial.printf("Auto-missing thumb %s\n", n.c_str()); qEnqueue(n); }
    }
    f=r.openNextFile(); heartbeat();
  }
}

// Delete every PNG inside /thumbs (keeps folder)
static void wipeThumbs(){
  File d=SD.open(TH_DIR);
  if(!d){ return; }
  File f=d.openNextFile();
  while(f){
    String p=f.name();
    if(!f.isDirectory()){
      if(p.endsWith(".png")) SD.remove(p);
    }
    f=d.openNextFile(); heartbeat();
  }
}

// ===== HTML =====
static String htmlHeader(const String& title, bool dark){
  String s;
  s += F("<!DOCTYPE html><html><head><meta charset='utf-8'/>"
       "<meta name='viewport' content='width=device-width,initial-scale=1'/>"
       "<title>");
  s += htmlEscape(title);
  s += F("</title><style>");
  if(dark) s += F(":root{--bg:#0b0e13;--card:#12161d;--muted:#1b212b;--text:#d7e0ea;--sub:#9db1c7;--accent:#6aa0ff;--danger:#ff6a6a;}");
  else     s += F(":root{--bg:#e9eef5;--card:#ffffff;--muted:#dfe7f1;--text:#1b2330;--sub:#51647a;--accent:#2f6dff;--danger:#d64242;}");
  s += F("body{font-family:system-ui,Segoe UI,Roboto,Inter,Arial;margin:16px;background:var(--bg);color:var(--text)}"
       "a{color:var(--accent);text-decoration:none} a:hover{text-decoration:underline}"
       ".top{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:12px}"
       ".chip{background:var(--muted);padding:6px 10px;border-radius:999px;color:var(--sub);font-size:12px}"
       ".panel{background:var(--card);border:1px solid #1e263233;border-radius:12px;padding:12px}"
       "table{border-collapse:collapse;width:100%;margin-top:8px}"
       "th,td{border-bottom:1px solid #1b233033;padding:8px;text-align:left;vertical-align:middle}"
       "th a{color:var(--text)} th a:hover{color:var(--accent)}"
       ".thumb{width:160px;height:120px;object-fit:contain;background:#ffffff;border:1px solid #1e263255;border-radius:8px}"
       ".btn{padding:6px 10px;border:1px solid #2b364777;border-radius:8px;display:inline-block;margin-right:6px}"
       ".btn.red{border-color:#5a1e1e;color:var(--danger)} .btn.blue{border-color:#233753;color:var(--accent)}"
       "#progress{width:100%;height:10px;background:var(--muted);border:1px solid #1e263244;border-radius:999px;overflow:hidden;display:none;margin-top:8px}"
       "#bar{width:0;height:100%;background:var(--accent)}"
       ".row{display:flex;gap:12px;flex-wrap:wrap;align-items:center}"
       "input[type=checkbox]{transform:scale(1.2);}"
       "</style></head><body>");
  return s;
}
static String htmlFooter(){ return F("</body></html>"); }

static void listDirItems(const String& dir, std::vector<Item>& out, uint32_t& counter, uint64_t& totalSize, uint32_t& fileCount){
  File d=SD.open(dir); if(!d||!d.isDirectory()) return;
  File f=d.openNextFile();
  while(f){
    String p=f.name(); bool isD=f.isDirectory();
    int slash=p.lastIndexOf('/'); String nameOnly=(slash>=0)?p.substring(slash+1):p;
    if(isD){ if(p==String(TH_DIR)) { f=d.openNextFile(); continue; } out.push_back({nameOnly,p,true,0,counter++}); }
    else{ if(hasSTLExt(p)){ out.push_back({nameOnly,p,false,(uint64_t)f.size(),counter++}); totalSize+=f.size(); fileCount+=1; } }
    f=d.openNextFile(); heartbeat();
  }
}
static String sortLink(const String& dir, const String& by, const String& curSort, const String& curOrder){
  String order="asc"; if(curSort==by && curOrder=="asc") order="desc";
  return "/?dir="+urlEncode(dir)+"&sort="+by+"&order="+order;
}

static void handleRoot(){
  String dir=sanitizeDir(server.hasArg("dir")? urlDecodeMin(server.arg("dir")): String(STL_DIR));
  String sort=server.hasArg("sort")? server.arg("sort"): "name";
  String order=server.hasArg("order")? server.arg("order"): "asc";
  String theme=server.hasArg("theme")? server.arg("theme"): "dark"; bool dark=(theme!="light");

  std::vector<Item> items; items.reserve(256);
  uint64_t totalSize=0; uint32_t fileCount=0; uint32_t counter=1;
  listDirItems(dir, items, counter, totalSize, fileCount);

  auto cmp=[&](const Item& a,const Item& b){
    if(a.isDir!=b.isDir) return a.isDir>b.isDir;
    int sgn=0;
    if(sort=="size") sgn=(a.size<b.size)?-1:((a.size>b.size)?1:0);
    else if(sort=="date") sgn=(a.pseudoTime<b.pseudoTime)?-1:((a.pseudoTime>b.pseudoTime)?1:0); // placeholder
    else sgn=ciCmp(a.name, b.name);
    return (order=="asc")?(sgn<0):(sgn>0);
  };
  std::sort(items.begin(), items.end(), cmp);

  uint64_t card=0;
  #if ARDUINO_ARCH_ESP32
  card = SD.cardSize(); // safe for display; may be 0 on some cards
  #endif
  uint64_t used=totalSize; uint64_t freeB=(card>used)?(card-used):0;

  String s=htmlHeader("ESP32-S3 FileHub", dark);
  IPAddress ip=(WiFi.getMode()==WIFI_MODE_STA)?WiFi.localIP():WiFi.softAPIP();
  s += "<div class='top row'>"
       "<div><b>ESP32-S3 SD FileHub</b> "
       "<span class='chip'>IP: "+ip.toString()+"</span> "
       "<span class='chip'>Used: "+htmlEscape(humanSize(used))+"</span> "
       "<span class='chip'>Free: "+htmlEscape(humanSize(freeB))+"</span> "
       "<span class='chip'>Total: "+htmlEscape(humanSize(card))+"</span>"
       "</div>"
       "<div class='row'><span class='chip' id='qst'>Queue: idle</span></div></div>";

  s += "<div class='panel row'>"
       "<form id='uform' method='POST' action='/upload' enctype='multipart/form-data'>"
       "<input type='hidden' name='dir' value='"+htmlEscape(dir)+"'>"
       "<input type='file' name='file' accept='.stl'> <input class='btn' type='submit' value='Upload'></form>"
       "<div id='progress'><div id='bar'></div></div><div id='status'></div>"
       "<form id='multi' method='POST'>"
       "<input type='hidden' name='dir' value='"+htmlEscape(dir)+"'>"
       "<button class='btn red' formaction='/delete-multi' type='submit'>Delete Selected</button>"
       "</form>"
       "<div class='chip'>Files: "+String(fileCount)+"</div>"
       "<div class='chip'>Total STL: "+htmlEscape(humanSize(totalSize))+"</div>"
       "</div>";

  s += "<div class='panel'><table>"
       "<tr><th></th><th>Preview</th>"
       "<th><a href='"+sortLink(dir,"name",sort,order)+"'>Name</a></th>"
       "<th><a href='"+sortLink(dir,"size",sort,order)+"'>Size</a></th>"
       "<th><a href='"+sortLink(dir,"date",sort,order)+"'>Date</a></th>"
       "<th>Actions</th></tr>";

  for(const auto& it: items){
    if(it.isDir){
      s += "<tr><td></td><td>📁</td>"
           "<td><a class='folder' href='/?dir="+urlEncode(it.path)+"&sort="+sort+"&order="+order+"&theme="+(dark?"dark":"light")+"'>"+htmlEscape(it.name)+"</a></td>"
           "<td>—</td><td>—</td><td></td></tr>";
    }else{
      String encName=urlEncode(it.path);
      String viewUrl="/view?name="+encName;

      // Thumbnail filename is deterministic (CRC of canonical path)
      String thumbPath = pngFor(it.path);
      String encThumb  = urlEncode(thumbPath);

      s += "<tr>";
      s += "<td><input form='multi' type='checkbox' name='sel' value='"+htmlEscape(it.path)+"'></td>";
      if (SD.exists(thumbPath)) {
        s += "<td><img class='thumb' src=\"/file?name="+encThumb+"\"/></td>";
      } else {
        s += "<td><div class='thumb'></div></td>";
      }
      s += "<td>"+htmlEscape(it.name)+"</td>"
           "<td>"+htmlEscape(humanSize(it.size))+"</td>"
           "<td>#"+String(it.pseudoTime)+"</td>"
           "<td><a class='btn' href='/download?name="+encName+"'>Download</a> "
           "<a class='btn blue' href='"+viewUrl+"'>Preview</a> "
           "<a class='btn red' href='/delete?name="+encName+"&dir="+urlEncode(dir)+"'>Delete</a></td></tr>";
    }
  }
  s += "</table></div>";

  s += R"JS(
<script>
const form=document.getElementById('uform'),st=document.getElementById('status'),pg=document.getElementById('progress'),bar=document.getElementById('bar');
form.addEventListener('submit',e=>{
  e.preventDefault();
  const fi=form.querySelector('input[type=file]'); if(!fi.files.length){st.textContent='No file';return;}
  const d=new FormData(form); st.textContent='Uploading...'; pg.style.display='block'; bar.style.width='0%';
  const x=new XMLHttpRequest(); x.open('POST','/upload',true);
  x.upload.onprogress=e=>{ if(e.lengthComputable) bar.style.width=(e.loaded/e.total*100).toFixed(1)+'%'; };
  x.onload=()=>{ if(x.status==200){ st.textContent='✅ Upload complete'; setTimeout(()=>location.reload(), 350); } else st.textContent='❌ Upload failed'; };
  x.onerror=()=>{ st.textContent='❌ Network error'; };
  x.send(d);
});
let _prevBusy=false;
setInterval(async()=>{
  try{
    const r=await fetch('/qstate'); const j=await r.json();
    const q=document.getElementById('qst');
    if(j.busy){
      const fname=decodeURIComponent(j.file||"");
      q.textContent=(fname? (fname+" — ") : "") + (j.task||"Working")+" "+((j.progress|0))+"%";
      st.textContent=(j.task? (j.task+": "):"")+(j.file||"")+(j.progress?(" ("+(j.progress|0)+"%)"):"");
      pg.style.display='block'; if(typeof j.progress==='number'){ bar.style.width=(j.progress|0)+'%'; }
      _prevBusy=true;
    }else{
      q.textContent='Queue: idle';
      if(_prevBusy){ location.reload(); } _prevBusy=false;
      if(bar) bar.style.width='0%'; if(pg) pg.style.display='none';
    }
  }catch(e){}
}, 900);
</script>
)JS";
  s += htmlFooter();
  server.send(200,"text/html; charset=utf-8",s);
}

// ===== File handling =====
static String ensureStlPathFromArg(const String& argName){
  String n=server.hasArg(argName)? urlDecodeMin(server.arg(argName)) : String();
  if(!n.length()) return String();
  String p=ensureSlash(n);
  if(!p.startsWith(STL_DIR)) p=joinPath(String(STL_DIR), p[0]=='/'? p.substring(1):p);
  return p;
}
static void handleFile(){
  String n = server.hasArg("name")? urlDecodeMin(server.arg("name")): String();
  if(!n.length()){ server.send(400,"text/plain","Bad request"); return; }
  n=ensureSlash(n);
  if(!SD.exists(n)){ server.send(404,"text/plain","Not found"); return; }
  File f=SD.open(n, FILE_READ);
  String lower=n; lower.toLowerCase();
  String ctype="application/octet-stream";
  if(lower.endsWith(".stl")) ctype="application/sla";
  else if(lower.endsWith(".png")) ctype="image/png";
  server.streamFile(f,ctype); f.close();
}
static void handleDownload(){
  String n=ensureStlPathFromArg("name");
  if(!n.length()||!SD.exists(n)){ server.send(404,"text/plain","Not found"); return; }
  File f=SD.open(n, FILE_READ); String fn=f.name(); if(fn.startsWith("/")) fn.remove(0,1);
  server.sendHeader("Content-Disposition","attachment; filename=\""+fn+"\"");
  server.streamFile(f,"application/octet-stream"); f.close();
}
static void handleDelete(){
  String n=ensureStlPathFromArg("name");
  String dir=sanitizeDir(server.hasArg("dir")? urlDecodeMin(server.arg("dir")): String(STL_DIR));
  if(n.length()&&SD.exists(n)) SD.remove(n);
  String png=pngFor(n); if(SD.exists(png)) SD.remove(png);
  server.sendHeader("Location","/?dir="+urlEncode(dir)); server.send(303);
}

// ===== Self-hosted 3D Preview (no CDN) =====
static void handleView(){
  String n=ensureStlPathFromArg("name");
  if(!n.length()||!SD.exists(n)){ server.send(404,"text/plain","Not found"); return; }
  String s=htmlHeader("Preview", true);
  s += "<div class='panel'><div style='display:flex;gap:10px;align-items:center;justify-content:space-between'>"
       "<div><b>Preview:</b> "+htmlEscape(n)+"</div>"
       "<div><a class='btn' href='/download?name="+urlEncode(n)+"'>Download STL</a></div>"
       "</div>"
       "<canvas id='cv' style='width:100%;height:70vh;border:1px solid #1e2632;background:#0e131b;border-radius:12px'></canvas>"
       "<div style='margin-top:8px;color:#9db1c7'>Drag to rotate • Wheel to zoom • Double-click to reset</div>"
       "</div>";
  s += "<script src='/stlview.js'></script>\n";
  s += "<script>initSTLViewer('cv', \"/file?name="+urlEncode(n)+"\");</script>";
  s += htmlFooter();
  server.send(200,"text/html; charset=utf-8",s);
}

static void handleStlViewJs(){
  const char* js = R"JS(
(function(){
  function parseASCII(txt){
    const V=[], N=[];
    const lines = txt.split(/\r?\n/);
    let nx=0,ny=0,nz=1, v=[], vi=0;
    for(let ln of lines){
      ln=ln.trim();
      if(!ln) continue;
      if(ln.startsWith('facet normal')){
        const m=ln.match(/-?\d+(\.\d+)?([eE][-+]?\d+)?/g);
        if(m && m.length>=3){ nx=+m[0]; ny=+m[1]; nz=+m[2]; }
        vi=0; v.length=0;
      }else if(ln.startsWith('vertex')){
        const m=ln.match(/-?\d+(\.\d+)?([eE][-+]?\d+)?/g);
        if(m && m.length>=3){
          v[vi++] = [+m[0], +m[1], +m[2]];
          if(vi===3){
            N.push([nx,ny,nz]);
            V.push(v[0], v[1], v[2]);
            vi=0; v.length=0;
          }
        }
      }
    }
    return {V,N};
  }
  function parseBinary(buf){
    const dv=new DataView(buf);
    if(dv.byteLength<84) return {V:[],N:[]};
    const tri=dv.getUint32(80,true);
    if(84+tri*50>dv.byteLength) return {V:[],N:[]};
    const V=[], N=[];
    let off=84;
    for(let i=0;i<tri;i++){
      const nx=dv.getFloat32(off+0,true), ny=dv.getFloat32(off+4,true), nz=dv.getFloat32(off+8,true); off+=12;
      const v0=[dv.getFloat32(off+0,true), dv.getFloat32(off+4,true), dv.getFloat32(off+8,true)]; off+=12;
      const v1=[dv.getFloat32(off+0,true), dv.getFloat32(off+4,true), dv.getFloat32(off+8,true)]; off+=12;
      const v2=[dv.getFloat32(off+0,true), dv.getFloat32(off+4,true), dv.getFloat32(off+8,true)]; off+=12;
      off+=2;
      N.push([nx,ny,nz]);
      V.push(v0,v1,v2);
    }
    return {V,N};
  }
  function rotXY(p, ax, ay){
    const sx=Math.sin(ax), cx=Math.cos(ax), sy=Math.sin(ay), cy=Math.cos(ay);
    let y=p[1]*cx - p[2]*sx;
    let z=p[1]*sx + p[2]*cx;
    let x= p[0]*cy + z*sy;
    z = -p[0]*sy + z*cy;
    return [x,y,z];
  }
  function normalizeVerts(V){
    if(V.length===0) return {V,scale:1,center:[0,0,0],diag:1};
    let xmin=1e9,xmax=-1e9,ymin=1e9,ymax=-1e9,zmin=1e9,zmax=-1e9;
    for(const p of V){
      const x=p[0],y=p[1],z=p[2];
      if(x<xmin)xmin=x; if(x>xmax)xmax=x;
      if(y<ymin)ymin=y; if(y>ymax)ymax=y;
      if(z<zmin)zmin=z; if(z>zmax)zmax=z;
    }
    const cx=(xmin+xmax)/2, cy=(ymin+ymax)/2, cz=(zmin+zmax)/2;
    const dx=xmax-xmin, dy=ymax-ymin, dz=zmax-zmin;
    const diag=Math.max(dx,dy,dz)||1;
    const scale=1/diag;
    const VV=V.map(p=>[ (p[0]-cx)*scale, (p[1]-cy)*scale, (p[2]-cz)*scale ]);
    return {V:VV, scale, center:[cx,cy,cz], diag};
  }
  function initSTLViewer(canvasId, url){
    const cv=document.getElementById(canvasId);
    const ctx=cv.getContext('2d');
    let W=0,H=0;
    function fit(){ const r=cv.getBoundingClientRect(); W=r.width|0; H=r.height|0; cv.width=W; cv.height=H; }
    fit(); window.addEventListener('resize', fit);

    let tris=[], norms=[];
    let ax=0.6, ay=0.7, zoom=1.8;

    function draw(){
      ctx.fillStyle='#0e131b'; ctx.fillRect(0,0,W,H);
      if(tris.length===0) return;
      const half = Math.min(W,H)*0.45*zoom;
      const L=[0.577,0.577,0.577];

      const T=[];
      for(let i=0;i<tris.length;i++){
        const t=tris[i];
        const r0=rotXY(t[0],ax,ay), r1=rotXY(t[1],ax,ay), r2=rotXY(t[2],ax,ay);
        const x0=r0[0]*half + W*0.5, y0=-r0[1]*half + H*0.5, z0=r0[2];
        const x1=r1[0]*half + W*0.5, y1=-r1[1]*half + H*0.5, z1=r1[2];
        const x2=r2[0]*half + W*0.5, y2=-r2[1]*half + H*0.5, z2=r2[2];
        const rn=rotXY(norms[i]||[0,0,1],ax,ay);
        const nl=Math.hypot(rn[0],rn[1],rn[2])||1;
        const nx=rn[0]/nl, ny=rn[1]/nl, nz=rn[2]/nl;
        const diffuse=Math.max(0, nx*L[0]+ny*L[1]+nz*L[2]);
        const spec=Math.pow(Math.max(0, nx*(L[0]+0)+ny*(L[1]+0)+nz*(L[2]+1)), 24);
        const rim=Math.pow(Math.max(0,1-Math.abs(nz)),1.2);
        let shade=0.10 + 0.88*diffuse + 0.50*spec + 0.18*rim; if(shade>1) shade=1;
        const c=Math.floor(200*shade+30);
        const fill='rgb('+c+','+c+','+c+')';
        const area=(x1-x0)*(y2-y0)-(y1-y0)*(x2-x0);
        if(area<=0) continue;
        const zavg=(z0+z1+z2)/3;
        T.push({x0,y0,x1,y1,x2,y2,z:zavg,fill});
      }

      T.sort((a,b)=>a.z-b.z);
      for(const t of T){
        ctx.beginPath();
        ctx.moveTo(t.x0,t.y0);
        ctx.lineTo(t.x1,t.y1);
        ctx.lineTo(t.x2,t.y2);
        ctx.closePath();
        ctx.fillStyle=t.fill;
        ctx.fill();
      }
    }

    let dragging=false, px=0, py=0;
    cv.addEventListener('mousedown', e=>{ dragging=true; px=e.clientX; py=e.clientY; });
    window.addEventListener('mouseup', ()=>dragging=false);
    window.addEventListener('mousemove', e=>{
      if(!dragging) return;
      const dx=(e.clientX-px), dy=(e.clientY-py);
      px=e.clientX; py=e.clientY;
      ay += dx*0.01; ax += dy*0.01; draw();
    });
    cv.addEventListener('wheel', e=>{
      e.preventDefault();
      zoom *= (e.deltaY>0)? 0.9 : 1.1;
      if(zoom<0.3) zoom=0.3; if(zoom>6) zoom=6; draw();
    }, {passive:false});
    cv.addEventListener('dblclick', ()=>{ ax=0.6; ay=0.7; zoom=1.8; draw(); });

    fetch(url).then(async r=>{
      const buf=await r.arrayBuffer();
      const head=new Uint8Array(buf,0,512);
      let asciiGuess=false; if(head.length>=5){
        const solid = (head[0]==115&&head[1]==111&&head[2]==108&&head[3]==105&&head[4]==100);
        let non=0; for(let i=0;i<head.length;i++){ const c=head[i]; if(c===9||c===10||c===13) continue; if(c<32||c>126) non++; }
        asciiGuess = solid && non<8;
      }
      let data;
      if(asciiGuess){
        const txt=new TextDecoder().decode(buf);
        data=parseASCII(txt);
      }else{
        data=parseBinary(buf);
      }
      const norm=normalizeVerts(data.V);

      tris=[]; norms=[];
      for(let i=0;i<norm.V.length;i+=3){
        tris.push([norm.V[i], norm.V[i+1], norm.V[i+2]]);
        norms.push(data.N[i/3] || [0,0,1]);
      }
      draw();
    }).catch(e=>{
      try{
        const ctx2=document.getElementById('cv').getContext('2d');
        ctx2.fillStyle='#fff'; ctx2.fillText('Error loading STL: '+e, 10, 20);
      }catch(_){}
      console.error(e);
    });

    return {redraw:draw};
  }
  window.initSTLViewer=initSTLViewer;
})();
)JS";
  server.send(200,"application/javascript; charset=utf-8", js);
}

// ===== Upload & multi (delete only) =====
static volatile bool g_uploadOK = false;
static void handleFileUpload(){
  static File f; static String lastName; static String uploadDir;
  HTTPUpload &u=server.upload();
  switch(u.status){
    case UPLOAD_FILE_START:{
      g_uploadOK=false;
      if(f) f.close();
      uploadDir = sanitizeDir(server.hasArg("dir") ? urlDecodeMin(server.arg("dir")) : String(STL_DIR));
      lastName = joinPath(uploadDir, u.filename);
      if(SD.exists(lastName)) SD.remove(lastName);
      f = SD.open(lastName, FILE_WRITE);
      break;
    }
    case UPLOAD_FILE_WRITE:
      if(f) f.write(u.buf, u.currentSize);
      break;
    case UPLOAD_FILE_END:
      if(f) f.close();
      if(hasSTLExt(lastName)){
        Serial.printf("Queued thumb %s\n", lastName.c_str());
        qEnqueue(lastName);
        // Reuse the same upload progress bar after upload is complete
        g_busy = true;
        setStatus("Waiting in queue", lastName, 0);
      }
      g_uploadOK = true;
      break;
    case UPLOAD_FILE_ABORTED:
      if(f){ f.close(); if(lastName.length()) SD.remove(lastName); }
      g_uploadOK=false;
      break;
    default: break;
  }
}
static void handleUploadDone(){
  if(g_uploadOK) server.send(200,"text/plain","OK");
  else           server.send(500,"text/plain","ABORTED");
}

static void handleDeleteMulti(){
  String dir=sanitizeDir(server.hasArg("dir")? urlDecodeMin(server.arg("dir")): String(STL_DIR));
  int n=server.args();
  for(int i=0;i<n;i++){
    if(server.argName(i)!="sel") continue;
    String p=ensureSlash(urlDecodeMin(server.arg(i)));
    if(!p.startsWith(STL_DIR)) p=joinPath(String(STL_DIR), p);
    if(SD.exists(p)) SD.remove(p);
    String png=pngFor(p); if(SD.exists(png)) SD.remove(png);
  }
  server.sendHeader("Location","/?dir="+urlEncode(dir)); server.send(303);
}

// ===== Queue state =====
static void handleQState(){
  String js = "{\"busy\":"; js += (g_busy?"true":"false");
  js += ",\"file\":\""; js += urlEncode(g_file); js += "\"";
  js += ",\"task\":\""; js += g_task; js += "\"";
  js += ",\"progress\":"; js += String(g_prog);
  js += ",\"status\":\""; js += g_statusLine; js += "\"";
  js += "}";
  server.send(200,"application/json", js);
}

// ===== Wi-Fi =====
static bool setupWiFi(){
  WiFi.mode(WIFI_STA); WiFi.begin(WIFI_SSID, WIFI_PASS); unsigned long t0=millis();
  while(WiFi.status()!=WL_CONNECTED && millis()-t0<10000){ delay(250); }
  if(WiFi.status()==WL_CONNECTED) return true;
  if(!ENABLE_AP_FALLBACK) return false;
  WiFi.mode(WIFI_AP); return WiFi.softAP(AP_SSID, AP_PASS);
}

// ===== Setup / Loop =====
void setup(){
  Serial.begin(115200); delay(300);
  Serial.println("ESP32-S3 STL FileHub — UTF-8 safe, 160x120 thumbs");

  SPI.begin(SD_SCK, SD_MISO, SD_MOSI, SD_CS);
  if(SD.begin(SD_CS, SPI, 10000000)) Serial.println("SD init OK"); else Serial.println("SD init FAIL");

  ensureDir(STL_DIR); ensureDir(TH_DIR);

  if(setupWiFi()){ Serial.print("WiFi IP: "); Serial.println((WiFi.getMode()==WIFI_MODE_STA)?WiFi.localIP():WiFi.softAPIP()); }
  else Serial.println("WiFi setup failed");

  server.on("/", handleRoot);
  server.on("/file", handleFile);
  server.on("/view", handleView);
  server.on("/download", handleDownload);
  server.on("/delete", handleDelete);
  server.on("/delete-multi", HTTP_POST, handleDeleteMulti);
  server.on("/upload", HTTP_POST, handleUploadDone, handleFileUpload);
  server.on("/stlview.js", handleStlViewJs);
  server.on("/thumb", [](){
    String n=ensureStlPathFromArg("name");
    if(!n.length()||!SD.exists(n)){ server.send(404,"text/plain","Not found"); return; }
    qEnqueue(n); server.send(200,"text/plain","ENQUEUED");
  });
  server.on("/qstate", handleQState);
  server.on("/favicon.ico", [](){ server.send(204); });
  server.begin(); Serial.println("HTTP server started.");

  if(REBUILD_THUMBS_ON_BOOT){
    Serial.println("Rebuilding thumbnails: wiping /thumbs and re-queuing all STLs...");
    wipeThumbs();
  }
  scanDirAndQueueMissing(String(STL_DIR));
}

void loop(){
  server.handleClient();
  static uint32_t lastRun=0;
  if(!qIsEmpty() && !g_qbusy && millis()-lastRun>20){
    g_qbusy=true; String n=qDequeue(); g_file=n; g_busy=true; g_task="Preparing"; g_prog=0; g_statusLine="Generating thumbnail: "+n; lastRun=millis();
    if(n.length()){
      String out=pngFor(n);
      Serial.printf("Thumb gen %s -> %s\n", n.c_str(), out.c_str());
      bool ok=generateThumbPNG(n.c_str(), out.c_str());
      Serial.println(ok?"OK":"FAIL");
    }
    g_busy=false; g_task=""; g_file=""; g_prog=0; g_statusLine=""; g_qbusy=false; delay(3);
  }
  delay(1);
}