// puzzle.cpp - Recherche de clés privées Bitcoin (secp256k1) multi-cibles, multi-cœurs, sans dépendance.
//
// Compilation : g++ -O3 -march=native -std=c++17 -o puzzle puzzle.cpp   (Linux : ajouter -pthread)
//               (-O3 et -march=native sont importants : sans eux le programme est 2 à 3 fois plus lent)
//
// Usage :
//   puzzle <clé_publique | adresse | cibles.txt | cibles.bloom> <bits> [address] [threads]
//   puzzle --genpub <clé_privée_hex> | --genaddr <clé_privée_hex>     (utilitaires de test)
//   address : à ajouter quand les cibles sont des adresses Bitcoin (1... ou bc1q...)
//g++ -O3 -march=native -std=c++17 -o puzzle puzzle.cpp
//puzzle.exe <clé_publique | cibles.txt | cibles.bloom> <bits>
//puzzle.exe <adresse | cibles.txt> <bits> address
// La clé recherchée est dans [2^(bits-1) , 2^bits - 1].
// cibles.txt   : une clé publique compressée par ligne -> construit et sauvegarde cibles.bloom
// cibles.bloom : filtre déjà construit (chargement direct)
// Modes de parcours (un par cœur) : Sobol, Aléatoire, Géométrique (2^i mod p), Monte Carlo.
#define _FILE_OFFSET_BITS 64
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <csignal>
#include <string>
#include <vector>
#include <algorithm>
#include <numeric>
#include <chrono>
#include <atomic>
#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#else
#include <thread>
#include <unistd.h>
#endif

typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;

struct U256 { u64 d[4]; };               // little-endian (d[0] = poids faible)
static const U256 ZERO = {{0,0,0,0}};
static const U256 ONE  = {{1,0,0,0}};
static const U256 PRIME = {{0xFFFFFFFEFFFFFC2FULL, ~0ULL, ~0ULL, ~0ULL}};
static const u64  KC = 0x1000003D1ULL;   // 2^256 mod p

// ---------------------------------------------------------------- 256 bits brut
static inline bool is_zero(const U256& a){ return (a.d[0]|a.d[1]|a.d[2]|a.d[3])==0; }
static inline bool eq(const U256& a,const U256& b){
    return ((a.d[0]^b.d[0])|(a.d[1]^b.d[1])|(a.d[2]^b.d[2])|(a.d[3]^b.d[3]))==0;
}
static inline bool geq(const U256& a,const U256& b){
    for(int i=3;i>=0;--i){ if(a.d[i]!=b.d[i]) return a.d[i]>b.d[i]; }
    return true;
}
static inline u64 add_raw(U256& r,const U256& a,const U256& b){
    u128 acc=0; u64 c=0;
    for(int i=0;i<4;i++){ acc=(u128)a.d[i]+b.d[i]+c; r.d[i]=(u64)acc; c=(u64)(acc>>64); }
    return c;
}
static inline u64 sub_raw(U256& r,const U256& a,const U256& b){
    u64 br=0;
    for(int i=0;i<4;i++){
        u128 t=(u128)a.d[i]-b.d[i]-br;
        r.d[i]=(u64)t; br=(u64)((t>>64)&1);
    }
    return br;
}
static inline void add_small(U256& a,u64 v){
    u128 acc=(u128)a.d[0]+v; a.d[0]=(u64)acc; u64 c=(u64)(acc>>64);
    for(int i=1;i<4;i++){ acc=(u128)a.d[i]+c; a.d[i]=(u64)acc; c=(u64)(acc>>64); }
}
static inline int get_bit(const U256& a,int i){ return (int)((a.d[i>>6]>>(i&63))&1); }
static int highest_bit(const U256& a){
    for(int i=255;i>=0;--i) if(get_bit(a,i)) return i;
    return -1;
}
static U256 shr2(U256 a){
    for(int i=0;i<4;i++){
        a.d[i]>>=2;
        if(i<3) a.d[i]|=a.d[i+1]<<62;   // a.d[i+1] n'a pas encore été décalé
    }
    return a;
}

// ---------------------------------------------------------------- hex / décimal
static bool parse_hex(const std::string& s,U256& out){
    if(s.empty()||s.size()>64) return false;
    out=ZERO;
    for(size_t i=0;i<s.size();i++){
        char c=s[s.size()-1-i]; int v;
        if(c>='0'&&c<='9') v=c-'0'; else if(c>='a'&&c<='f') v=c-'a'+10;
        else if(c>='A'&&c<='F') v=c-'A'+10; else return false;
        out.d[i/16]|=(u64)v<<((i%16)*4);
    }
    return true;
}
static std::string to_hex(const U256& a){
    char buf[65];
    snprintf(buf,sizeof buf,"%016llx%016llx%016llx%016llx",
        (unsigned long long)a.d[3],(unsigned long long)a.d[2],
        (unsigned long long)a.d[1],(unsigned long long)a.d[0]);
    return buf;
}
static std::string to_dec(U256 a){
    if(is_zero(a)) return "0";
    std::vector<u64> parts;
    while(!is_zero(a)){
        u128 rem=0;
        for(int i=3;i>=0;--i){
            u128 cur=(rem<<64)|a.d[i];
            a.d[i]=(u64)(cur/1000000000ULL);
            rem=cur%1000000000ULL;
        }
        parts.push_back((u64)rem);
    }
    char buf[32]; std::string s;
    snprintf(buf,sizeof buf,"%llu",(unsigned long long)parts.back()); s+=buf;
    for(int i=(int)parts.size()-2;i>=0;--i){ snprintf(buf,sizeof buf,"%09llu",(unsigned long long)parts[i]); s+=buf; }
    return s;
}

// ---------------------------------------------------------------- corps Fp (p = 2^256 - 2^32 - 977)
static inline void fe_add(U256& r,const U256& a,const U256& b){
    U256 t; u64 c=add_raw(t,a,b);
    if(c){ U256 k={{KC,0,0,0}}; add_raw(t,t,k); }
    if(geq(t,PRIME)) sub_raw(t,t,PRIME);
    r=t;
}
static inline void fe_sub(U256& r,const U256& a,const U256& b){
    U256 t; u64 br=sub_raw(t,a,b);
    if(br){ U256 k={{KC,0,0,0}}; sub_raw(t,t,k); }
    r=t;
}
// Réduction d'un produit de 512 bits modulo p (2^256 = 2^32 + 977 mod p)
static inline void fe_reduce(U256& r,const u64* t){
    u64 r5[5]; u64 carry=0;
    for(int i=0;i<4;i++){
        u128 acc=(u128)t[4+i]*KC+t[i]+carry;
        r5[i]=(u64)acc; carry=(u64)(acc>>64);
    }
    r5[4]=carry;
    U256 res; u128 acc=(u128)r5[4]*KC+r5[0];
    res.d[0]=(u64)acc; carry=(u64)(acc>>64);
    for(int i=1;i<4;i++){ acc=(u128)r5[i]+carry; res.d[i]=(u64)acc; carry=(u64)(acc>>64); }
    if(carry){
        acc=(u128)res.d[0]+KC; res.d[0]=(u64)acc; carry=(u64)(acc>>64);
        for(int i=1;i<4;i++){ acc=(u128)res.d[i]+carry; res.d[i]=(u64)acc; carry=(u64)(acc>>64); }
    }
    if(geq(res,PRIME)) sub_raw(res,res,PRIME);
    r=res;
}
static inline void fe_mul(U256& r,const U256& a,const U256& b){
    u64 t[8]={0,0,0,0,0,0,0,0};
    for(int i=0;i<4;i++){
        u64 carry=0;
        for(int j=0;j<4;j++){
            u128 acc=(u128)a.d[i]*b.d[j]+t[i+j]+carry;
            t[i+j]=(u64)acc; carry=(u64)(acc>>64);
        }
        t[i+4]=carry;
    }
    fe_reduce(r,t);
}
// Carré dédié : 10 produits de 64 bits au lieu de 16
static inline void fe_sqr(U256& r,const U256& a){
    u64 t[8]={0,0,0,0,0,0,0,0};
    for(int i=0;i<3;i++){
        u64 carry=0;
        for(int j=i+1;j<4;j++){
            u128 acc=(u128)a.d[i]*a.d[j]+t[i+j]+carry;
            t[i+j]=(u64)acc; carry=(u64)(acc>>64);
        }
        t[i+4]=carry;
    }
    u64 c=0;
    for(int k=0;k<8;k++){ u64 v=t[k]; t[k]=(v<<1)|c; c=v>>63; }
    u64 carry=0;
    for(int i=0;i<4;i++){
        u128 acc=(u128)a.d[i]*a.d[i]+t[2*i]+carry;
        t[2*i]=(u64)acc; carry=(u64)(acc>>64);
        acc=(u128)t[2*i+1]+carry;
        t[2*i+1]=(u64)acc; carry=(u64)(acc>>64);
    }
    fe_reduce(r,t);
}
static inline void fe_sqr_n(U256& r,const U256& a,int n){
    U256 t=a; for(int i=0;i<n;i++) fe_sqr(t,t); r=t;
}
static U256 fe_pow(const U256& base,const U256& e){
    U256 r=ONE; int top=highest_bit(e);
    for(int i=top;i>=0;--i){ fe_sqr(r,r); if(get_bit(e,i)) fe_mul(r,r,base); }
    return r;
}
// Inverse modulaire a^(p-2) par chaîne d'additions : 255 carrés + 15 produits
static U256 fe_inv(const U256& a){
    U256 x2,x3,x6,x9,x11,x22,x44,x88,x176,x220,x223,t;
    fe_sqr(x2,a); fe_mul(x2,x2,a);
    fe_sqr(x3,x2); fe_mul(x3,x3,a);
    fe_sqr_n(x6,x3,3); fe_mul(x6,x6,x3);
    fe_sqr_n(x9,x6,3); fe_mul(x9,x9,x3);
    fe_sqr_n(x11,x9,2); fe_mul(x11,x11,x2);
    fe_sqr_n(x22,x11,11); fe_mul(x22,x22,x11);
    fe_sqr_n(x44,x22,22); fe_mul(x44,x44,x22);
    fe_sqr_n(x88,x44,44); fe_mul(x88,x88,x44);
    fe_sqr_n(x176,x88,88); fe_mul(x176,x176,x88);
    fe_sqr_n(x220,x176,44); fe_mul(x220,x220,x44);
    fe_sqr_n(x223,x220,3); fe_mul(x223,x223,x3);
    fe_sqr_n(t,x223,23); fe_mul(t,t,x22);
    fe_sqr_n(t,t,5); fe_mul(t,t,a);
    fe_sqr_n(t,t,3); fe_mul(t,t,x2);
    fe_sqr_n(t,t,2); fe_mul(t,t,a);
    return t;
}

// ---------------------------------------------------------------- courbe y^2 = x^3 + 7
struct Aff { U256 x,y; bool inf; };
struct Jac { U256 X,Y,Z; bool inf; };

static Aff GEN;
static const char* GX_HEX="79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798";
static const char* GY_HEX="483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";

static bool on_curve(const Aff& P){
    U256 l,r; fe_sqr(l,P.y); fe_sqr(r,P.x); fe_mul(r,r,P.x);
    U256 seven={{7,0,0,0}}; fe_add(r,r,seven);
    return eq(l,r);
}

// --- Arithmétique affine (lente, 1 inversion par opération) : sert à la vérification indépendante
static Aff aff_add(const Aff& P,const Aff& Q){
    if(P.inf) return Q;
    if(Q.inf) return P;
    U256 l;
    if(eq(P.x,Q.x)){
        if(!eq(P.y,Q.y) || is_zero(P.y)){ Aff o; o.x=ZERO;o.y=ZERO;o.inf=true; return o; }
        U256 n,d; fe_sqr(n,P.x); U256 n3; fe_add(n3,n,n); fe_add(n3,n3,n);   // 3x^2
        fe_add(d,P.y,P.y);
        fe_mul(l,n3,fe_inv(d));
    } else {
        U256 n,d; fe_sub(n,Q.y,P.y); fe_sub(d,Q.x,P.x);
        fe_mul(l,n,fe_inv(d));
    }
    Aff R; R.inf=false;
    fe_sqr(R.x,l); fe_sub(R.x,R.x,P.x); fe_sub(R.x,R.x,Q.x);
    U256 t; fe_sub(t,P.x,R.x); fe_mul(R.y,l,t); fe_sub(R.y,R.y,P.y);
    return R;
}
static Aff aff_mul(const U256& k,const Aff& P){
    Aff R; R.x=ZERO;R.y=ZERO;R.inf=true;
    for(int i=highest_bit(k);i>=0;--i){
        R=aff_add(R,R);
        if(get_bit(k,i)) R=aff_add(R,P);
    }
    return R;
}

// --- Arithmétique Jacobienne (rapide) : sert au calcul du point de départ
static Jac jac_dbl(const Jac& P){
    if(P.inf||is_zero(P.Y)){ Jac o; o.X=o.Y=o.Z=ZERO; o.inf=true; return o; }
    U256 A,B,C,D,E,F,t,t2;
    fe_sqr(A,P.X); fe_sqr(B,P.Y); fe_sqr(C,B);
    fe_add(t,P.X,B); fe_sqr(t,t); fe_sub(t,t,A); fe_sub(t,t,C); fe_add(D,t,t);
    fe_add(E,A,A); fe_add(E,E,A);
    fe_sqr(F,E);
    Jac R; R.inf=false;
    fe_add(t,D,D); fe_sub(R.X,F,t);
    fe_sub(t,D,R.X); fe_mul(t,E,t);
    fe_add(t2,C,C); fe_add(t2,t2,t2); fe_add(t2,t2,t2);   // 8C
    fe_sub(R.Y,t,t2);
    fe_mul(t,P.Y,P.Z); fe_add(R.Z,t,t);
    return R;
}
static Jac jac_madd(const Jac& P,const Aff& Q){
    if(P.inf){ Jac R; R.X=Q.x;R.Y=Q.y;R.Z=ONE;R.inf=false; return R; }
    U256 Z1Z1,U2,S2,H,HH,I,J,r,V,t;
    fe_sqr(Z1Z1,P.Z); fe_mul(U2,Q.x,Z1Z1);
    fe_mul(S2,Q.y,P.Z); fe_mul(S2,S2,Z1Z1);
    fe_sub(H,U2,P.X);
    fe_sub(t,S2,P.Y); fe_add(r,t,t);
    if(is_zero(H)){
        if(is_zero(r)) return jac_dbl(P);
        Jac o; o.X=o.Y=o.Z=ZERO; o.inf=true; return o;
    }
    fe_sqr(HH,H); fe_add(I,HH,HH); fe_add(I,I,I);
    fe_mul(J,H,I); fe_mul(V,P.X,I);
    Jac R; R.inf=false;
    fe_sqr(R.X,r); fe_sub(R.X,R.X,J); fe_sub(R.X,R.X,V); fe_sub(R.X,R.X,V);
    fe_sub(t,V,R.X); fe_mul(t,r,t);
    U256 u; fe_mul(u,P.Y,J); fe_add(u,u,u);
    fe_sub(R.Y,t,u);
    fe_add(t,P.Z,H); fe_sqr(t,t); fe_sub(t,t,Z1Z1); fe_sub(R.Z,t,HH);
    return R;
}
static Jac jac_mul(const U256& k,const Aff& P){
    Jac R; R.X=R.Y=R.Z=ZERO; R.inf=true;
    for(int i=highest_bit(k);i>=0;--i){
        R=jac_dbl(R);
        if(get_bit(k,i)) R=jac_madd(R,P);
    }
    return R;
}
static Aff jac_to_aff(const Jac& J){
    Aff A; A.x=ZERO;A.y=ZERO;
    if(J.inf){ A.inf=true; return A; }
    U256 zi=fe_inv(J.Z),zi2,zi3;
    fe_sqr(zi2,zi); fe_mul(zi3,zi2,zi);
    fe_mul(A.x,J.X,zi2); fe_mul(A.y,J.Y,zi3); A.inf=false;
    return A;
}

// ---------------------------------------------------------------- utilitaires divers
static std::string compress_hex(const Aff& P){
    return std::string(((P.y.d[0]&1)?"03":"02"))+to_hex(P.x);
}
static inline u64 splitmix(u64& s){
    u64 z=(s+=0x9E3779B97F4A7C15ULL);
    z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL; z=(z^(z>>27))*0x94D049BB133111EBULL;
    return z^(z>>31);
}
struct Rng {
    u64 s[4];
    void seed(u64 v){ for(int i=0;i<4;i++) s[i]=splitmix(v); }
    static inline u64 rotl(u64 x,int k){ return (x<<k)|(x>>(64-k)); }
    u64 next(){
        u64 r=rotl(s[1]*5,7)*9, t=s[1]<<17;
        s[2]^=s[0]; s[3]^=s[1]; s[1]^=s[2]; s[0]^=s[3]; s[2]^=t; s[3]=rotl(s[3],45);
        return r;
    }
};
struct SpinLock {
    std::atomic_flag f=ATOMIC_FLAG_INIT;
    void lock(){ while(f.test_and_set(std::memory_order_acquire)){} }
    void unlock(){ f.clear(std::memory_order_release); }
};
static U256 shl_u64(u64 v,int sh){
    U256 r=ZERO; int limb=sh>>6, off=sh&63;
    if(limb<4) r.d[limb]|=v<<off;
    if(off && limb+1<4) r.d[limb+1]|=v>>(64-off);
    return r;
}
static U256 low_mask(int nbits){           // 2^nbits - 1
    U256 r=ZERO;
    for(int b=0;b<nbits;b++) r.d[b>>6]|=1ULL<<(b&63);
    return r;
}
static std::string fmt_int(u64 v){
    std::string s=std::to_string(v), o;
    int c=0;
    for(int i=(int)s.size()-1;i>=0;--i){ o.insert(o.begin(),s[i]); if(++c%3==0&&i>0) o.insert(o.begin(),' '); }
    return o;
}
static std::string fmt_keys(long double v){
    const char* u[]={"","K","M","G","T","P","E"};
    int i=0; while(v>=1000.0L && i<6){ v/=1000.0L; i++; }
    char b[32]; snprintf(b,sizeof b,i?"%.2Lf %s":"%.0Lf %s",v,u[i]); return b;
}
static std::string fmt_time(long double s){
    char b[64];
    if(s<0||s!=s) return "?";
    if(s>3.15e9L) return ">100 ans";
    unsigned long long t=(unsigned long long)s;
    unsigned long long y=t/31536000ULL; t%=31536000ULL;
    unsigned long long d=t/86400, h=(t%86400)/3600, m=(t%3600)/60, sec=t%60;
    if(y) snprintf(b,sizeof b,"%llu an(s) %llu j",y,d);
    else if(d) snprintf(b,sizeof b,"%llu j %02lluh %02llum",d,h,m);
    else snprintf(b,sizeof b,"%02llu:%02llu:%02llu",h,m,sec);
    return b;
}
static std::string short_hex(const U256& v){
    std::string h=to_hex(v); size_t p=h.find_first_not_of('0');
    h=(p==std::string::npos)?"0":h.substr(p);
    if(h.size()>22) h=h.substr(0,10)+"…"+h.substr(h.size()-10);
    return "0x"+h;
}

// ---------------------------------------------------------------- SHA-256 / RIPEMD-160 (un seul bloc) et adresses
static inline u32 rotr32(u32 x,int n){ return (x>>n)|(x<<(32-n)); }
static inline u32 rotl32(u32 x,int n){ return (x<<n)|(x>>(32-n)); }
static const u32 SHA_K[64]={
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};

// SHA-256 d'un message tenant dans un seul bloc (w = 16 mots big-endian déjà préparés)
static inline void sha256_block(const u32* w16,u32* out){
    u32 w[64];
    for(int i=0;i<16;i++) w[i]=w16[i];
    #pragma GCC unroll 64
    for(int i=16;i<64;i++){
        u32 s0=rotr32(w[i-15],7)^rotr32(w[i-15],18)^(w[i-15]>>3);
        u32 s1=rotr32(w[i-2],17)^rotr32(w[i-2],19)^(w[i-2]>>10);
        w[i]=w[i-16]+s0+w[i-7]+s1;
    }
    u32 a=0x6a09e667,b=0xbb67ae85,c=0x3c6ef372,d=0xa54ff53a,e=0x510e527f,f=0x9b05688c,g=0x1f83d9ab,h=0x5be0cd19;
    #pragma GCC unroll 64
    for(int i=0;i<64;i++){
        u32 S1=rotr32(e,6)^rotr32(e,11)^rotr32(e,25), ch=(e&f)^(~e&g);
        u32 t1=h+S1+ch+SHA_K[i]+w[i];
        u32 S0=rotr32(a,2)^rotr32(a,13)^rotr32(a,22), mj=(a&b)^(a&c)^(b&c);
        u32 t2=S0+mj;
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    out[0]=a+0x6a09e667; out[1]=b+0xbb67ae85; out[2]=c+0x3c6ef372; out[3]=d+0xa54ff53a;
    out[4]=e+0x510e527f; out[5]=f+0x9b05688c; out[6]=g+0x1f83d9ab; out[7]=h+0x5be0cd19;
}
// SHA-256 d'un message de n <= 55 octets (octet par octet)
static void sha256_bytes(const unsigned char* m,size_t n,unsigned char* out32){
    unsigned char buf[64]; memset(buf,0,64); memcpy(buf,m,n); buf[n]=0x80;
    u64 bl=(u64)n*8; for(int i=0;i<8;i++) buf[63-i]=(unsigned char)(bl>>(8*i));
    u32 w[16],o[8];
    for(int i=0;i<16;i++) w[i]=((u32)buf[4*i]<<24)|((u32)buf[4*i+1]<<16)|((u32)buf[4*i+2]<<8)|buf[4*i+3];
    sha256_block(w,o);
    for(int i=0;i<8;i++){ out32[4*i]=o[i]>>24; out32[4*i+1]=o[i]>>16; out32[4*i+2]=o[i]>>8; out32[4*i+3]=o[i]; }
}

static const unsigned char RMD_R1[80]={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15, 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
    3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12, 1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2, 4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13};
static const unsigned char RMD_R2[80]={5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12, 6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
    15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13, 8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14, 12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11};
static const unsigned char RMD_S1[80]={11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8, 7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
    11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5, 11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12, 9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6};
static const unsigned char RMD_S2[80]={8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6, 9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
    9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5, 15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8, 8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11};
static const u32 RMD_K1[5]={0x00000000,0x5A827999,0x6ED9EBA1,0x8F1BBCDC,0xA953FD4E};
static const u32 RMD_K2[5]={0x50A28BE6,0x5C4DD124,0x6D703EF3,0x7A6D76E9,0x00000000};
template<int F> static inline u32 rmd_f(u32 x,u32 y,u32 z){
    if(F==0) return x^y^z;
    if(F==1) return (x&y)|(~x&z);
    if(F==2) return (x|~y)^z;
    if(F==3) return (x&z)|(y&~z);
    return x^(y|~z);
}
// RIPEMD-160 d'un message tenant dans un seul bloc (X = 16 mots little-endian)
template<int F> static inline void rmd_seg(const u32* X,u32& a,u32& b,u32& c,u32& d,u32& e,
                                           u32& a2,u32& b2,u32& c2,u32& d2,u32& e2){
    #pragma GCC unroll 16
    for(int j=16*F;j<16*F+16;j++){
        u32 t=rotl32(a+rmd_f<F>(b,c,d)+X[RMD_R1[j]]+RMD_K1[F],RMD_S1[j])+e;
        a=e; e=d; d=rotl32(c,10); c=b; b=t;
        t=rotl32(a2+rmd_f<4-F>(b2,c2,d2)+X[RMD_R2[j]]+RMD_K2[F],RMD_S2[j])+e2;
        a2=e2; e2=d2; d2=rotl32(c2,10); c2=b2; b2=t;
    }
}
static inline void rmd160_block(const u32* X,u32* out){
    u32 a=0x67452301,b=0xEFCDAB89,c=0x98BADCFE,d=0x10325476,e=0xC3D2E1F0;
    u32 a2=a,b2=b,c2=c,d2=d,e2=e;
    rmd_seg<0>(X,a,b,c,d,e,a2,b2,c2,d2,e2);
    rmd_seg<1>(X,a,b,c,d,e,a2,b2,c2,d2,e2);
    rmd_seg<2>(X,a,b,c,d,e,a2,b2,c2,d2,e2);
    rmd_seg<3>(X,a,b,c,d,e,a2,b2,c2,d2,e2);
    rmd_seg<4>(X,a,b,c,d,e,a2,b2,c2,d2,e2);
    const u32 I0=0x67452301u, I1=0xEFCDAB89u, I2=0x98BADCFEu, I3=0x10325476u, I4=0xC3D2E1F0u;
    u32 t=I1+c+d2;
    out[1]=I2+d+e2; out[2]=I3+e+a2; out[3]=I4+a+b2; out[4]=I0+b+c2; out[0]=t;
}
// hash160 empaqueté dans un U256 : lecture little-endian des 20 octets du condensat
static inline U256 pack_rmd(const u32* h){
    U256 r; r.d[0]=h[0]|((u64)h[1]<<32); r.d[1]=h[2]|((u64)h[3]<<32); r.d[2]=h[4]; r.d[3]=0; return r;
}
static U256 pack20(const unsigned char* b){
    U256 r=ZERO; memcpy(&r.d[0],b,8); memcpy(&r.d[1],b+8,8); u32 t; memcpy(&t,b+16,4); r.d[2]=t; return r;
}
static void unpack20(const U256& h,unsigned char* b){
    memcpy(b,&h.d[0],8); memcpy(b+8,&h.d[1],8); u32 t=(u32)h.d[2]; memcpy(b+16,&t,4);
}
// Chemin rapide (boucle de recherche) : hash160 de la clé publique compressée (parité de Y, X)
static inline U256 hash160_fast(const U256& x,u64 par){
    u32 X[8];
    X[0]=(u32)(x.d[3]>>32); X[1]=(u32)x.d[3]; X[2]=(u32)(x.d[2]>>32); X[3]=(u32)x.d[2];
    X[4]=(u32)(x.d[1]>>32); X[5]=(u32)x.d[1]; X[6]=(u32)(x.d[0]>>32); X[7]=(u32)x.d[0];
    u32 w[16],H[8],rw[16],o[5];
    w[0]=((0x02u+(u32)par)<<24)|(X[0]>>8);
    for(int i=1;i<8;i++) w[i]=(X[i-1]<<24)|(X[i]>>8);
    w[8]=(X[7]<<24)|0x00800000u;
    for(int i=9;i<15;i++) w[i]=0;
    w[15]=264;
    sha256_block(w,H);
    for(int i=0;i<8;i++) rw[i]=__builtin_bswap32(H[i]);
    rw[8]=0x80; for(int i=9;i<14;i++) rw[i]=0; rw[14]=256; rw[15]=0;
    rmd160_block(rw,o);
    return pack_rmd(o);
}
// Chemin "octets" (vérifications indépendantes)
static void pub33(const U256& x,u64 par,unsigned char* out){
    out[0]=(unsigned char)(2+par);
    for(int i=0;i<32;i++) out[1+i]=(unsigned char)(x.d[3-i/8]>>(56-8*(i%8)));
}
static void hash160_bytes(const unsigned char* m,size_t n,unsigned char* out20){
    unsigned char dg[32]; sha256_bytes(m,n,dg);
    u32 X[16]={0},o[5];
    for(int i=0;i<8;i++) X[i]=(u32)dg[4*i]|((u32)dg[4*i+1]<<8)|((u32)dg[4*i+2]<<16)|((u32)dg[4*i+3]<<24);
    X[8]=0x80; X[14]=256;
    rmd160_block(X,o);
    for(int i=0;i<5;i++){ out20[4*i]=o[i]; out20[4*i+1]=o[i]>>8; out20[4*i+2]=o[i]>>16; out20[4*i+3]=o[i]>>24; }
}
static U256 hash160_point_bytes(const Aff& P){
    unsigned char pb[33],h[20]; pub33(P.x,P.y.d[0]&1,pb); hash160_bytes(pb,33,h); return pack20(h);
}

// ---- hash160 de plusieurs clés à la fois (vecteurs SIMD via les extensions GCC/Clang)
#if defined(VLANES)
#elif defined(_WIN32)
#define VLANES 4          // 128 bits : évite les soucis d'alignement de pile 32 octets de MinGW
#else
#define VLANES 8          // 256 bits (AVX2 si -march=native)
#endif
typedef u32 vu __attribute__((vector_size(4*VLANES)));
static inline vu vsplat(u32 x){ vu v; for(int i=0;i<VLANES;i++) v[i]=x; return v; }
#define VROTR(x,n) (((x)>>(n))|((x)<<(32-(n))))
#define VROTL(x,n) (((x)<<(n))|((x)>>(32-(n))))
template<int F> static inline vu rmd_fv(vu x,vu y,vu z){
    if(F==0) return x^y^z;
    if(F==1) return (x&y)|(~x&z);
    if(F==2) return (x|~y)^z;
    if(F==3) return (x&z)|(y&~z);
    return x^(y|~z);
}
template<int F> static inline void rmd_segv(const vu* X,vu& a,vu& b,vu& c,vu& d,vu& e,vu& a2,vu& b2,vu& c2,vu& d2,vu& e2){
    #pragma GCC unroll 16
    for(int j=16*F;j<16*F+16;j++){
        vu t=VROTL(a+rmd_fv<F>(b,c,d)+X[RMD_R1[j]]+vsplat(RMD_K1[F]),RMD_S1[j])+e;
        a=e; e=d; d=VROTL(c,10); c=b; b=t;
        t=VROTL(a2+rmd_fv<4-F>(b2,c2,d2)+X[RMD_R2[j]]+vsplat(RMD_K2[F]),RMD_S2[j])+e2;
        a2=e2; e2=d2; d2=VROTL(c2,10); c2=b2; b2=t;
    }
}
// hash160 de VLANES clés publiques compressées (xs[l], pars[l]) -> out[l] (même empaquetage que hash160_fast)
static void hash160_vec(const U256* xs,const u64* pars,U256* out){
    u32 Xl[8][VLANES], Pl[VLANES];
    for(int l=0;l<VLANES;l++){
        const U256& x=xs[l];
        Xl[0][l]=(u32)(x.d[3]>>32); Xl[1][l]=(u32)x.d[3]; Xl[2][l]=(u32)(x.d[2]>>32); Xl[3][l]=(u32)x.d[2];
        Xl[4][l]=(u32)(x.d[1]>>32); Xl[5][l]=(u32)x.d[1]; Xl[6][l]=(u32)(x.d[0]>>32); Xl[7][l]=(u32)x.d[0];
        Pl[l]=0x02u+(u32)pars[l];
    }
    vu X[8],w[64],H[8],rw[16];
    for(int i=0;i<8;i++) memcpy(&X[i],Xl[i],sizeof(vu));
    vu P; memcpy(&P,Pl,sizeof(vu));
    w[0]=(P<<24)|(X[0]>>8);
    for(int i=1;i<8;i++) w[i]=(X[i-1]<<24)|(X[i]>>8);
    w[8]=(X[7]<<24)|vsplat(0x00800000u);
    for(int i=9;i<15;i++) w[i]=vsplat(0);
    w[15]=vsplat(264);
    #pragma GCC unroll 64
    for(int i=16;i<64;i++){
        vu s0=VROTR(w[i-15],7)^VROTR(w[i-15],18)^(w[i-15]>>3);
        vu s1=VROTR(w[i-2],17)^VROTR(w[i-2],19)^(w[i-2]>>10);
        w[i]=w[i-16]+s0+w[i-7]+s1;
    }
    vu a=vsplat(0x6a09e667u),b=vsplat(0xbb67ae85u),c=vsplat(0x3c6ef372u),d=vsplat(0xa54ff53au);
    vu e=vsplat(0x510e527fu),f=vsplat(0x9b05688cu),g=vsplat(0x1f83d9abu),h=vsplat(0x5be0cd19u);
    #pragma GCC unroll 64
    for(int i=0;i<64;i++){
        vu S1=VROTR(e,6)^VROTR(e,11)^VROTR(e,25), ch=(e&f)^(~e&g);
        vu t1=h+S1+ch+vsplat(SHA_K[i])+w[i];
        vu S0=VROTR(a,2)^VROTR(a,13)^VROTR(a,22), mj=(a&b)^(a&c)^(b&c);
        vu t2=S0+mj;
        h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    H[0]=a+vsplat(0x6a09e667u); H[1]=b+vsplat(0xbb67ae85u); H[2]=c+vsplat(0x3c6ef372u); H[3]=d+vsplat(0xa54ff53au);
    H[4]=e+vsplat(0x510e527fu); H[5]=f+vsplat(0x9b05688cu); H[6]=g+vsplat(0x1f83d9abu); H[7]=h+vsplat(0x5be0cd19u);
    for(int i=0;i<8;i++){
        vu q=H[i];
        rw[i]=(q>>24)|((q>>8)&vsplat(0x0000FF00u))|((q<<8)&vsplat(0x00FF0000u))|(q<<24);
    }
    rw[8]=vsplat(0x80); for(int i=9;i<14;i++) rw[i]=vsplat(0); rw[14]=vsplat(256); rw[15]=vsplat(0);
    vu a1=vsplat(0x67452301u),b1=vsplat(0xEFCDAB89u),c1=vsplat(0x98BADCFEu),d1=vsplat(0x10325476u),e1=vsplat(0xC3D2E1F0u);
    vu a2=a1,b2=b1,c2=c1,d2=d1,e2=e1;
    rmd_segv<0>(rw,a1,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    rmd_segv<1>(rw,a1,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    rmd_segv<2>(rw,a1,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    rmd_segv<3>(rw,a1,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    rmd_segv<4>(rw,a1,b1,c1,d1,e1,a2,b2,c2,d2,e2);
    vu o[5];
    o[0]=vsplat(0xEFCDAB89u)+c1+d2; o[1]=vsplat(0x98BADCFEu)+d1+e2; o[2]=vsplat(0x10325476u)+e1+a2;
    o[3]=vsplat(0xC3D2E1F0u)+a1+b2; o[4]=vsplat(0x67452301u)+b1+c2;
    u32 T[5][VLANES];
    for(int k=0;k<5;k++) memcpy(T[k],&o[k],sizeof(vu));
    for(int l=0;l<VLANES;l++){
        out[l].d[0]=T[0][l]|((u64)T[1][l]<<32); out[l].d[1]=T[2][l]|((u64)T[3][l]<<32);
        out[l].d[2]=T[4][l]; out[l].d[3]=0;
    }
}

// ---- Base58Check (P2PKH) et Bech32 (P2WPKH)
static const char* B58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
static std::string b58check_encode(unsigned char version,const unsigned char* h20){
    std::vector<unsigned char> d(25); d[0]=version; memcpy(&d[1],h20,20);
    unsigned char s1[32],s2[32]; sha256_bytes(d.data(),21,s1); sha256_bytes(s1,32,s2); memcpy(&d[21],s2,4);
    size_t zeros=0; while(zeros<d.size()&&d[zeros]==0) zeros++;
    std::vector<unsigned char> num(d.begin()+zeros,d.end()); std::string out;
    while(!num.empty()){
        std::vector<unsigned char> q; unsigned rem=0;
        for(unsigned char c:num){ unsigned cur=rem*256+c; unsigned qb=cur/58; rem=cur%58; if(!q.empty()||qb) q.push_back((unsigned char)qb); }
        out.push_back(B58[rem]); num=q;
    }
    out.append(zeros,'1'); std::reverse(out.begin(),out.end());
    return out;
}
// 0 = invalide, 1 = P2PKH valide (h20 rempli), 2 = valide mais non supporté (P2SH ...)
static int b58check_decode(const std::string& s,unsigned char* h20){
    if(s.empty()||s.size()>40) return 0;
    std::vector<unsigned char> num;                      // little-endian
    size_t zeros=0; while(zeros<s.size()&&s[zeros]=='1') zeros++;
    for(char ch:s){
        const char* p=strchr(B58,ch); if(!p||!ch) return 0;
        unsigned carry=(unsigned)(p-B58);
        for(size_t j=0;j<num.size();j++){ carry+=(unsigned)num[j]*58; num[j]=(unsigned char)carry; carry>>=8; }
        while(carry){ num.push_back((unsigned char)carry); carry>>=8; }
    }
    std::vector<unsigned char> d(zeros,0); d.insert(d.end(),num.rbegin(),num.rend());
    if(d.size()!=25) return 0;
    unsigned char s1[32],s2[32]; sha256_bytes(d.data(),21,s1); sha256_bytes(s1,32,s2);
    if(memcmp(s2,&d[21],4)!=0) return 0;
    if(d[0]!=0x00) return 2;
    memcpy(h20,&d[1],20); return 1;
}
static const char* B32="qpzry9x8gf2tvdw0s3jn54khce6mua7l";
static u32 bech32_polymod(const std::vector<unsigned char>& v){
    static const u32 G[5]={0x3b6a57b2,0x26508e6d,0x1ea119fa,0x3d4233dd,0x2a1462b3};
    u32 chk=1;
    for(unsigned char x:v){ u32 b=chk>>25; chk=((chk&0x1ffffff)<<5)^x; for(int i=0;i<5;i++) if((b>>i)&1) chk^=G[i]; }
    return chk;
}
static std::vector<unsigned char> bech32_hrp_expand(const std::string& hrp){
    std::vector<unsigned char> v; for(char c:hrp) v.push_back((unsigned char)c>>5);
    v.push_back(0); for(char c:hrp) v.push_back((unsigned char)c&31); return v;
}
static std::string bech32_encode_p2wpkh(const unsigned char* h20){
    std::vector<unsigned char> data; data.push_back(0);
    int acc=0,bits=0;
    for(int i=0;i<20;i++){ acc=(acc<<8)|h20[i]; bits+=8; while(bits>=5){ bits-=5; data.push_back((acc>>bits)&31); } }
    if(bits) data.push_back((acc<<(5-bits))&31);
    std::vector<unsigned char> v=bech32_hrp_expand("bc"); v.insert(v.end(),data.begin(),data.end());
    for(int i=0;i<6;i++) v.push_back(0);
    u32 pm=bech32_polymod(v)^1;
    for(int i=0;i<6;i++) data.push_back((pm>>(5*(5-i)))&31);
    std::string out="bc1"; for(unsigned char x:data) out.push_back(B32[x]);
    return out;
}
static int bech32_decode_addr(const std::string& s0,unsigned char* h20){
    if(s0.size()<14||s0.size()>90) return 0;
    bool lo=false,up=false; for(char c:s0){ if(c>='a'&&c<='z') lo=true; if(c>='A'&&c<='Z') up=true; }
    if(lo&&up) return 0;
    std::string s=s0; for(auto& c:s) if(c>='A'&&c<='Z') c+=32;
    size_t pos=s.rfind('1'); if(pos==std::string::npos||pos<1||s.size()-pos<7) return 0;
    std::string hrp=s.substr(0,pos); std::vector<unsigned char> data;
    for(size_t i=pos+1;i<s.size();i++){ const char* p=strchr(B32,s[i]); if(!p||!s[i]) return 0; data.push_back((unsigned char)(p-B32)); }
    std::vector<unsigned char> v=bech32_hrp_expand(hrp); v.insert(v.end(),data.begin(),data.end());
    u32 pm=bech32_polymod(v);
    if(pm!=1&&pm!=0x2bc830a3) return 0;
    if(hrp!="bc") return 0;
    data.resize(data.size()-6);
    if(data.empty()) return 0;
    if(data[0]!=0||pm!=1) return 2;                      // taproot (v1+) ... : non supporté
    std::vector<unsigned char> prog; int acc=0,bits=0;
    for(size_t i=1;i<data.size();i++){ acc=(acc<<5)|data[i]; bits+=5; if(bits>=8){ bits-=8; prog.push_back((acc>>bits)&255); } }
    if(bits>=5||((acc<<(8-bits))&255)) return 0;
    if(prog.size()!=20) return 2;                        // P2WSH (32 octets) : non supporté
    memcpy(h20,prog.data(),20); return 1;
}
// ---------------------------------------------------------------- ensemble de cibles (Bloom + liste exacte)
struct Ent { U256 x; u64 par; };                       // X de la clé publique + parité de Y (0 = préfixe 02, 1 = 03)
static_assert(sizeof(Ent)==40,"taille Ent");
static inline bool x_less(const U256& a,const U256& b){
    for(int i=3;i>=0;--i){ if(a.d[i]!=b.d[i]) return a.d[i]<b.d[i]; }
    return false;
}
static bool ent_less(const Ent& a,const Ent& b){
    if(!eq(a.x,b.x)) return x_less(a.x,b.x);
    return a.par<b.par;
}
struct TargetSet {
    std::vector<Ent> list;                              // triée, sans doublon
    std::vector<u64> bloom;                             // nblocks * 8 mots de 64 bits (blocs de 512 bits)
    u64 nblocks=0;
    u64 src_hash=0;
    bool addr=false;                                    // true : la liste contient des hash160 (adresses)
};
// Filtre de Bloom "par blocs" : 1 bloc (une ligne de cache) par test, 6 bits par clé.
// X est uniforme : on lit directement ses bits, sans fonction de hachage.
static inline bool bloom_test(const u64* bl,u64 mask,const U256& x){
    const u64* blk=bl+((x.d[0]&mask)<<3);
    u64 h=x.d[1];
    for(int j=0;j<6;j++){
        u64 p=(h>>(9*j))&511;
        if(!((blk[p>>6]>>(p&63))&1)) return false;
    }
    return true;
}
static inline void bloom_insert(u64* bl,u64 mask,const U256& x){
    u64* blk=bl+((x.d[0]&mask)<<3);
    u64 h=x.d[1];
    for(int j=0;j<6;j++){ u64 p=(h>>(9*j))&511; blk[p>>6]|=1ULL<<(p&63); }
}
static void build_bloom(TargetSet& ts){
    u64 n=ts.list.size(), need=(n+15)/16; if(need<1) need=1;
    u64 nb=1; while(nb<need) nb<<=1;
    ts.nblocks=nb; ts.bloom.assign(nb*8,0);
    for(const Ent& e:ts.list) bloom_insert(ts.bloom.data(),nb-1,e.x);
}
static void finalize_targets(TargetSet& ts){
    std::sort(ts.list.begin(),ts.list.end(),ent_less);
    ts.list.erase(std::unique(ts.list.begin(),ts.list.end(),
        [](const Ent& a,const Ent& b){ return eq(a.x,b.x)&&a.par==b.par; }),ts.list.end());
    build_bloom(ts);
}
static bool ts_has_x(const TargetSet& ts,const U256& x){
    Ent probe; probe.x=x; probe.par=0;
    auto it=std::lower_bound(ts.list.begin(),ts.list.end(),probe,ent_less);
    return it!=ts.list.end() && eq(it->x,x);
}
static bool ts_has_exact(const TargetSet& ts,const U256& x,u64 par){
    Ent probe; probe.x=x; probe.par=par;
    return std::binary_search(ts.list.begin(),ts.list.end(),probe,ent_less);
}
static std::string ent_hex(const Ent& e){ return std::string(e.par?"03":"02")+to_hex(e.x); }
static std::string ent_hash_hex(const Ent& e){
    unsigned char b[20]; unpack20(e.x,b); char s[41]; for(int i=0;i<20;i++) snprintf(s+2*i,3,"%02x",b[i]); return s;
}
static std::string ent_addr_legacy(const Ent& e){ unsigned char b[20]; unpack20(e.x,b); return b58check_encode(0x00,b); }
static std::string ent_addr_bech32(const Ent& e){ unsigned char b[20]; unpack20(e.x,b); return bech32_encode_p2wpkh(b); }
static std::string ent_text(const TargetSet& ts,const Ent& e){ return ts.addr? ent_addr_legacy(e) : ent_hex(e); }
// Adresse -> Ent (hash160 empaqueté). Retour : 0 invalide, 1 ok, 2 valide mais non supportée (P2SH, P2WSH, Taproot)
static int parse_address(const std::string& s,Ent& e){
    unsigned char h[20];
    int r=b58check_decode(s,h);
    if(r==0) r=bech32_decode_addr(s,h);
    if(r==1){ e.x=pack20(h); e.par=0; }
    return r;
}

static bool parse_pub(const std::string& s,Ent& e){
    if(s.size()!=66||s[0]!='0'||(s[1]!='2'&&s[1]!='3')) return false;
    U256 x; if(!parse_hex(s.substr(2),x)||geq(x,PRIME)) return false;
    static U256 ex; static bool init=false;
    if(!init){ ex=PRIME; add_small(ex,1); ex=shr2(ex); init=true; }
    U256 r,y,y2; fe_sqr(r,x); fe_mul(r,r,x); U256 seven={{7,0,0,0}}; fe_add(r,r,seven);
    y=fe_pow(r,ex); fe_sqr(y2,y);
    if(!eq(y2,r)) return false;                          // X n'est pas sur la courbe
    e.x=x; e.par=(s[1]=='3'); return true;
}
static void parse_targets_text(const std::string& txt,TargetSet& ts,bool addr,u64& lines,u64& rejected,u64& dups,u64& unsupported){
    lines=rejected=dups=unsupported=0; ts.addr=addr;
    size_t i=0;
    if(txt.size()>=3&&(unsigned char)txt[0]==0xEF&&(unsigned char)txt[1]==0xBB&&(unsigned char)txt[2]==0xBF) i=3;
    while(i<txt.size()){
        size_t j=txt.find('\n',i); if(j==std::string::npos) j=txt.size();
        size_t a=i,b=j;
        while(a<b&&(txt[a]==' '||txt[a]=='\t'||txt[a]=='\r')) a++;
        size_t t=a; while(t<b&&txt[t]!=' '&&txt[t]!='\t'&&txt[t]!='\r') t++;   // 1er mot de la ligne
        if(t>a){
            lines++;
            Ent e; std::string tok=txt.substr(a,t-a);
            if(addr){
                int rc=parse_address(tok,e);
                if(rc==1) ts.list.push_back(e); else if(rc==2) unsupported++; else rejected++;
            } else if(parse_pub(tok,e)) ts.list.push_back(e); else rejected++;
        }
        i=j+1;
    }
    u64 valid=ts.list.size();
    finalize_targets(ts);
    dups=valid-ts.list.size();
}
static bool read_file(const std::string& path,std::string& out){
    FILE* f=fopen(path.c_str(),"rb"); if(!f) return false;
    out.clear(); char buf[1<<16]; size_t n;
    while((n=fread(buf,1,sizeof buf,f))>0) out.append(buf,n);
    fclose(f); return true;
}
static u64 fnv64(const std::string& s){
    u64 h=1469598103934665603ULL;
    for(unsigned char c:s){ h^=c; h*=1099511628211ULL; }
    return h;
}
static u64 sum_hash(const void* p,size_t n,u64 h){
    const unsigned char* c=(const unsigned char*)p; size_t i=0;
    for(;i+8<=n;i+=8){ u64 w; memcpy(&w,c+i,8); h=(h^w)*0x9E3779B97F4A7C15ULL; h^=h>>29; }
    for(;i<n;i++){ h=(h^c[i])*0x100000001B3ULL; }
    return h;
}

// Fichier .bloom : en-tête (6 x u64) + filtre + liste exacte
static const char MAGIC[8]={'P','Z','B','L','O','O','M','2'};
static const u64 ENDIAN_TAG=0x0102030405060708ULL;
static u64 payload_sum(const TargetSet& ts){
    u64 h=0x1234567812345678ULL;
    h=sum_hash(ts.bloom.data(),ts.bloom.size()*8,h);
    h=sum_hash(ts.list.data(),ts.list.size()*sizeof(Ent),h);
    return h;
}
static bool save_bloom(const TargetSet& ts,const std::string& path){
    FILE* f=fopen(path.c_str(),"wb"); if(!f) return false;
    u64 hdr[6]={ENDIAN_TAG,(u64)ts.list.size(),ts.nblocks,ts.src_hash,payload_sum(ts),(u64)(ts.addr?1:0)};
    bool ok=fwrite(MAGIC,1,8,f)==8 && fwrite(hdr,8,6,f)==6
        && fwrite(ts.bloom.data(),8,ts.bloom.size(),f)==ts.bloom.size()
        && fwrite(ts.list.data(),sizeof(Ent),ts.list.size(),f)==ts.list.size();
    ok=(fclose(f)==0)&&ok;
    return ok;
}
static bool load_bloom(const std::string& path,TargetSet& ts,std::string& err){
    FILE* f=fopen(path.c_str(),"rb"); if(!f){ err="fichier introuvable"; return false; }
    char mg[8]; u64 hdr[6];
    if(fread(mg,1,8,f)!=8||memcmp(mg,MAGIC,8)!=0||fread(hdr,8,6,f)!=6){ fclose(f); err="format invalide"; return false; }
    if(hdr[0]!=ENDIAN_TAG){ fclose(f); err="format d'octets incompatible"; return false; }
    u64 n=hdr[1], nb=hdr[2];
    if(n==0||n>(1ULL<<32)||nb==0||(nb&(nb-1))||nb>(1ULL<<32)){ fclose(f); err="en-tête incohérent"; return false; }
    ts.nblocks=nb; ts.src_hash=hdr[3]; ts.addr=(hdr[5]==1);
    ts.bloom.assign(nb*8,0); ts.list.assign(n,Ent());
    bool ok=fread(ts.bloom.data(),8,ts.bloom.size(),f)==ts.bloom.size()
         && fread(ts.list.data(),sizeof(Ent),n,f)==n;
    char extra; if(ok && fread(&extra,1,1,f)==1) ok=false;          // fichier trop long
    fclose(f);
    if(!ok){ err="fichier tronqué ou corrompu"; return false; }
    if(payload_sum(ts)!=hdr[4]){ err="somme de contrôle invalide"; return false; }
    for(size_t i=0;i<n;i++){
        if(i&&!ent_less(ts.list[i-1],ts.list[i])){ err="liste non triée"; return false; }
        if(!bloom_test(ts.bloom.data(),nb-1,ts.list[i].x)){ err="filtre incohérent"; return false; }
    }
    return true;
}

// ---------------------------------------------------------------- recherche : état partagé
static const int HALF=512;                 // chaque lot teste 2*HALF clés consécutives autour d'un point central
static std::vector<U256> gx,gy;            // i*G pour i = 1..HALF
static Aff SST;                            // (2*HALF)*G : pas vers le lot suivant

static void build_tables(){
    gx.assign(HALF+1,ZERO); gy.assign(HALF+1,ZERO);
    Aff cur=GEN;
    for(int i=1;i<=HALF;i++){ gx[i]=cur.x; gy[i]=cur.y; if(i<HALF) cur=aff_add(cur,GEN); }
    SST=aff_add(cur,cur);                  // cur = HALF*G
}

struct Found { U256 key; Ent ent; std::string pub; double t; };
struct TState {
    std::atomic<u64> keys; std::atomic<u64> block; std::atomic<int> mode;
    char pad[40];
    TState():keys(0),block(0),mode(-1){}
};
typedef std::chrono::steady_clock clk;

struct Run {
    const TargetSet* ts=nullptr;
    int bits=0,nthreads=1,bsize=0,nbl=0;
    U256 start,end,blockmask;
    u64 NB=1, prime=0;
    std::vector<std::atomic<u64>> claim;                // blocs déjà pris par un cœur
    std::vector<TState> st;
    std::atomic<bool> stop; std::atomic<int> done;
    SpinLock lock; std::vector<Found> found;
    bool write_file=false;
    clk::time_point t0;
    Run():stop(false),done(0){}
};

static bool is_prime_u64(u64 n){
    if(n<2) return false;
    for(u64 d=2;d*d<=n;d++) if(n%d==0) return false;
    return true;
}
static u64 mod_pow(u64 b,u64 e,u64 m){
    u64 r=1%m; b%=m;
    while(e){ if(e&1) r=(u64)((u128)r*b%m); b=(u64)((u128)b*b%m); e>>=1; }
    return r;
}
static bool two_is_primitive(u64 p){
    u64 m=p-1; std::vector<u64> fs;
    for(u64 d=2;d*d<=m;d++) if(m%d==0){ fs.push_back(d); while(m%d==0) m/=d; }
    if(m>1) fs.push_back(m);
    for(u64 q:fs) if(mod_pow(2,(p-1)/q,p)==1) return false;
    return true;
}

static void init_run(Run& r,int bits,int nthreads,const TargetSet* ts,bool write_file){
    r.ts=ts; r.bits=bits; r.nthreads=nthreads; r.write_file=write_file;
    r.start=ZERO; r.start.d[(bits-1)>>6]|=1ULL<<((bits-1)&63);
    r.end=low_mask(bits);
    int range_bits=bits-1;
    int b=(range_bits>=6)? std::min(20,range_bits-6) : 0;
    if(range_bits-b>26) b=range_bits-26;                // au plus 2^26 blocs
    r.bsize=b; r.nbl=range_bits-b; r.NB=1ULL<<r.nbl;
    r.blockmask=low_mask(b);
    u64 nw=(r.NB+63)/64;
    r.claim=std::vector<std::atomic<u64>>(nw);
    for(u64 i=0;i<nw;i++) r.claim[i].store(0);
    for(u64 bb=r.NB;bb<nw*64;bb++) r.claim[bb>>6].fetch_or(1ULL<<(bb&63));   // bits hors plage = déjà pris
    r.st=std::vector<TState>(nthreads);
    r.found.clear(); r.stop=false; r.done=0;
    r.prime=0;
    if(r.NB>=8){ u64 p=r.NB+1; while(!(is_prime_u64(p)&&two_is_primitive(p))) p++; r.prime=p; }
}

static inline bool claim_block(Run& r,u64 b){
    std::atomic<u64>& w=r.claim[b>>6]; u64 m=1ULL<<(b&63);
    if(w.load(std::memory_order_relaxed)&m) return false;
    return !(w.fetch_or(m)&m);
}
static inline u64 rev_bits(u64 v,int nb){
    u64 r=0; for(int i=0;i<nb;i++){ r=(r<<1)|(v&1); v>>=1; } return r;
}

// Générateurs d'ordre de blocs : 0 Sobol, 1 Aléatoire, 2 Géométrique (2^i mod p), 3 Monte Carlo
static const char* MODE_NAME[4]={"Sobol","Aléatoire","Géométrique","Monte Carlo"};
struct Gen {
    Run* r; int type; Rng rng;
    u64 n0=0,it=0,resid=0,ZS=1,hits=0; size_t pos=0;
    std::vector<u32> order;
    Gen(Run* rr,int t,int tid):r(rr),type(t){
        rng.seed((u64)clk::now().time_since_epoch().count()*0x9E3779B97F4A7C15ULL+(u64)tid*7919+(u64)t*104729);
        if(type==2&&r->NB<8) type=0;
        u64 NB=r->NB;
        n0=(NB*(u64)tid)/(u64)r->nthreads;
        if(type==2){ u64 p=r->prime; resid=mod_pow(2,((p-1)*(u64)tid)/(u64)r->nthreads,p); }
        if(type==3){
            u64 Z=std::min<u64>(NB,4096); ZS=NB/Z;
            order.resize(Z); std::iota(order.begin(),order.end(),0u);
            for(size_t i=order.size();i>1;--i) std::swap(order[i-1],order[rng.next()%i]);
        }
    }
    bool next(u64& blk){
        u64 NB=r->NB;
        if(type==0){
            while(it<NB){
                u64 n=(n0+it)&(NB-1); it++;
                u64 b=rev_bits(n^(n>>1),r->nbl);       // Sobol (dimension 1, ordre de Gray)
                if(claim_block(*r,b)){ blk=b; return true; }
            }
            return false;
        }
        if(type==1){
            for(int t=0;t<16;t++){ u64 b=rng.next()&(NB-1); if(claim_block(*r,b)){ blk=b; return true; } }
            u64 nw=r->claim.size(), w0=rng.next()%nw;   // fin de parcours : cherche un bloc libre
            for(u64 j=0;j<nw;j++){
                u64 w=(w0+j)%nw; u64 cur=r->claim[w].load();
                while(~cur){
                    u64 b=w*64+(u64)__builtin_ctzll(~cur);
                    if(claim_block(*r,b)){ blk=b; return true; }
                    cur=r->claim[w].load();
                }
            }
            return false;
        }
        if(type==2){
            u64 p=r->prime;
            while(it<p-1){
                u64 b=resid-1; resid=(resid*2)%p; it++;
                if(b<NB&&claim_block(*r,b)){ blk=b; return true; }
            }
            return false;
        }
        for(;;){                                         // Monte Carlo : zones égales, ordre aléatoire
            if(pos>=order.size()){
                if(pos>0&&hits==0) return false;
                for(size_t i=order.size();i>1;--i) std::swap(order[i-1],order[rng.next()%i]);
                pos=0; hits=0;
            }
            u64 base=(u64)order[pos++]*ZS;
            for(int t=0;t<8;t++){ u64 b=base+(rng.next()&(ZS-1)); if(claim_block(*r,b)){ hits++; blk=b; return true; } }
            u64 off=rng.next()&(ZS-1);
            for(u64 j=0;j<ZS;j++){ u64 b=base+((off+j)&(ZS-1)); if(claim_block(*r,b)){ hits++; blk=b; return true; } }
        }
    }
};

// ---------------------------------------------------------------- résultat trouvé
static Ent ent_of_point(bool addr,const Aff& P){
    Ent e;
    if(addr){ e.x=hash160_point_bytes(P); e.par=0; }
    else { e.x=P.x; e.par=P.y.d[0]&1; }
    return e;
}
static void record_find(Run& r,const U256& key,const Aff& P){
    r.lock.lock();
    for(const Found& f:r.found) if(eq(f.key,key)){ r.lock.unlock(); return; }
    Found f; f.key=key; f.ent=ent_of_point(r.ts->addr,P); f.pub=compress_hex(P);
    f.t=std::chrono::duration<double>(clk::now()-r.t0).count();
    r.found.push_back(f);
    if(r.write_file){
        FILE* fo=fopen("cle_trouvee.txt","a");
        if(fo){
            if(r.ts->addr){
                fprintf(fo,"Adresse (P2PKH)     : %s\n",ent_addr_legacy(f.ent).c_str());
                fprintf(fo,"Adresse (bech32)    : %s\n",ent_addr_bech32(f.ent).c_str());
                fprintf(fo,"Hash160             : %s\n",ent_hash_hex(f.ent).c_str());
            }
            fprintf(fo,"Clé publique        : %s\n",f.pub.c_str());
            fprintf(fo,"Bits                : %d\n",r.bits);
            fprintf(fo,"Clé privée (hex)    : %s\n",to_hex(key).c_str());
            fprintf(fo,"Clé privée (décimal): %s\n",to_dec(key).c_str());
            fprintf(fo,"Vérification        : VALIDE\n");
            fprintf(fo,"Temps (s)           : %.1f\n",f.t);
            fprintf(fo,"----------------------------------------\n");
            fclose(fo);
        }
    }
    if(r.found.size()>=r.ts->list.size()) r.stop.store(true);
    r.lock.unlock();
}
// Confirmation indépendante : k*G recalculé en arithmétique affine (et hash160 par le chemin "octets"),
// puis comparaison exacte avec la liste des cibles.
static void verify_point(Run& r,const U256& k){
    if(is_zero(k)) return;
    Aff P=aff_mul(k,GEN);
    if(P.inf) return;
    bool hit=r.ts->addr ? ts_has_exact(*r.ts,hash160_point_bytes(P),0)
                        : ts_has_exact(*r.ts,P.x,P.y.d[0]&1);
    if(hit) record_find(r,k,P);
}

struct Scratch {
    std::vector<U256> pre,cx; std::vector<char> zero; std::vector<u64> cpar; std::vector<int> coff;
    Scratch():pre(HALF+2),cx(2*HALF+2*VLANES+2),zero(HALF+2),cpar(2*HALF+2*VLANES+2),coff(2*HALF+2*VLANES+2){}
};

// Parcourt [start,end] (un bloc) par lots de 2*HALF clés consécutives.
// Un point central C sert aux clés kc-i et kc+i : une seule inversion (par lots) pour deux clés.
template<bool ADDR>
static void search_block(Run& r,const U256& start,const U256& end,Scratch& sc,TState& st){
    const TargetSet& ts=*r.ts;
    const u64* bl=ts.bloom.data(); const u64 mask=ts.nblocks-1;
    U256 lo=start, kc=start; add_small(kc,(u64)HALF);          // clés du lot : kc-HALF .. kc+HALF-1
    Aff C=jac_to_aff(jac_mul(kc,GEN));
    for(;;){
        if(r.stop.load(std::memory_order_relaxed)) return;
        U256 diff; sub_raw(diff,end,lo);
        bool last=((diff.d[1]|diff.d[2]|diff.d[3])==0) && diff.d[0]<(u64)(2*HALF);
        u64 count=last? diff.d[0]+1 : (u64)(2*HALF);
        int nc=0;
        auto key_of=[&](int off){ U256 k=kc; if(off>=0) add_small(k,(u64)off); else { U256 m={{(u64)(-off),0,0,0}}; sub_raw(k,kc,m); } return k; };
        auto emit=[&](const U256& x,u64 par,int off){
            if(ADDR){ sc.cx[nc]=x; sc.cpar[nc]=par; sc.coff[nc]=off; nc++; }
            else if(bloom_test(bl,mask,x) && ts_has_x(ts,x)) verify_point(r,key_of(off));
        };
        emit(C.x,C.y.d[0]&1,0);                                   // clé centrale

        // inversion par lots de (gx[i]-C.x), i = 1..HALF, puis du pas vers le lot suivant
        U256 acc=ONE;
        for(int i=1;i<=HALF;i++){
            U256 d; fe_sub(d,gx[i],C.x);
            if(is_zero(d)){ sc.zero[i]=1; d=ONE; } else sc.zero[i]=0;
            fe_mul(acc,acc,d); sc.pre[i]=acc;
        }
        U256 dS; fe_sub(dS,SST.x,C.x);
        bool zs=is_zero(dS); if(zs) dS=ONE;
        fe_mul(acc,acc,dS);
        U256 inv=fe_inv(acc);
        Aff Cn; Cn.inf=false; Cn.x=ZERO; Cn.y=ZERO;
        {
            U256 invd; fe_mul(invd,inv,sc.pre[HALF]); fe_mul(inv,inv,dS);
            if(!zs&&!last){
                U256 t,l; fe_sub(t,SST.y,C.y); fe_mul(l,t,invd);
                fe_sqr(Cn.x,l); fe_sub(Cn.x,Cn.x,C.x); fe_sub(Cn.x,Cn.x,SST.x);
                fe_sub(t,C.x,Cn.x); fe_mul(Cn.y,l,t); fe_sub(Cn.y,Cn.y,C.y);
            }
        }
        for(int i=HALF;i>=1;--i){
            U256 invd;
            if(i>1){
                fe_mul(invd,inv,sc.pre[i-1]);
                U256 d; fe_sub(d,gx[i],C.x); if(sc.zero[i]) d=ONE;
                fe_mul(inv,inv,d);
            } else invd=inv;
            if(sc.zero[i]){                                       // cas dégénéré (C = ±i*G) : chemin lent sûr
                if(i<HALF) verify_point(r,key_of(i));
                verify_point(r,key_of(-i));
                continue;
            }
            U256 t,l,x3,y3;
            // clé kc-i : C + (-iG)
            fe_add(t,gy[i],C.y); fe_mul(l,t,invd);
            fe_sqr(x3,l); fe_sub(x3,x3,C.x); fe_sub(x3,x3,gx[i]);
            u64 par=0;
            if(ADDR){ fe_sub(t,x3,C.x); fe_mul(y3,l,t); fe_sub(y3,y3,C.y); par=y3.d[0]&1; }
            emit(x3,par,-i);
            if(i<HALF){                                           // clé kc+i : C + iG
                fe_sub(t,gy[i],C.y); fe_mul(l,t,invd);
                fe_sqr(x3,l); fe_sub(x3,x3,C.x); fe_sub(x3,x3,gx[i]);
                if(ADDR){ fe_sub(t,C.x,x3); fe_mul(y3,l,t); fe_sub(y3,y3,C.y); par=y3.d[0]&1; }
                emit(x3,par,i);
            }
        }
        if(ADDR){                                                 // hash160 par paquets de VLANES clés
            for(int c=0;c<nc;c+=VLANES){
                U256 xs[VLANES],hs[VLANES]; u64 ps[VLANES]; int m=std::min(VLANES,nc-c);
                for(int l=0;l<VLANES;l++){ int idx=c+(l<m?l:m-1); xs[l]=sc.cx[idx]; ps[l]=sc.cpar[idx]; }
                hash160_vec(xs,ps,hs);
                for(int l=0;l<m;l++)
                    if(bloom_test(bl,mask,hs[l]) && ts_has_x(ts,hs[l])) verify_point(r,key_of(sc.coff[c+l]));
            }
        }
        st.keys.fetch_add(count,std::memory_order_relaxed);
        if(last) break;
        add_small(lo,(u64)(2*HALF)); add_small(kc,(u64)(2*HALF));
        if(zs) C=jac_to_aff(jac_mul(kc,GEN)); else C=Cn;
    }
}

struct WArg { Run* r; int tid; };
static void worker(WArg* a){
    Run& r=*a->r; int tid=a->tid; TState& st=r.st[tid];
    std::vector<Gen> gens;
    if(r.nthreads>=4) gens.emplace_back(&r,tid%4,tid);                      // 1 mode par cœur
    else for(int m=0;m<4;m++) gens.emplace_back(&r,m,tid);                  // moins de 4 cœurs : alternance
    Scratch sc; size_t idx=0;
    while(!r.stop.load()){
        Gen& g=gens[idx%gens.size()]; u64 blk;
        if(!g.next(blk)) break;                                              // tous les blocs sont pris
        st.mode.store(g.type); st.block.store(blk);
        U256 s=r.start; add_raw(s,s,shl_u64(blk,r.bsize));
        U256 e; add_raw(e,s,r.blockmask);
        if(r.ts->addr) search_block<true>(r,s,e,sc,st); else search_block<false>(r,s,e,sc,st);
        idx++;
    }
    st.mode.store(-1);
    r.done.fetch_add(1);
}
#ifdef _WIN32
static DWORD WINAPI thread_main(LPVOID p){ worker((WArg*)p); return 0; }
static int hw_threads(){ SYSTEM_INFO si; GetSystemInfo(&si); return (int)si.dwNumberOfProcessors; }
static void sleep_ms(int ms){ Sleep(ms); }
#else
static int hw_threads(){ int n=(int)std::thread::hardware_concurrency(); return n>0?n:1; }
static void sleep_ms(int ms){ std::this_thread::sleep_for(std::chrono::milliseconds(ms)); }
#endif

// ---------------------------------------------------------------- affichage
static bool g_ansi=false;
static std::atomic<bool> g_sigint(false);
static void on_sigint(int){ g_sigint.store(true); }
static const char* CL(const char* c){ return g_ansi?c:""; }
static const int INNER=74;
static int vis_len(const std::string& s){
    int n=0;
    for(size_t i=0;i<s.size();){
        unsigned char c=s[i];
        if(c==0x1b){ while(i<s.size()&&s[i]!='m') i++; i++; continue; }
        if((c&0xC0)!=0x80) n++;
        i++;
    }
    return n;
}
static std::string rep(const char* s,int n){ std::string o; for(int i=0;i<n;i++) o+=s; return o; }
static std::string row(const std::string& c){
    std::string o=std::string(CL("\x1b[90m"))+"║"+CL("\x1b[0m")+" "+c;
    int v=vis_len(c); if(v<INNER) o.append(INNER-v,' ');
    o+=std::string(" ")+CL("\x1b[90m")+"║"+CL("\x1b[0m")+"\n";
    return o;
}
static std::string border(const char* l,const char* m,const char* rr){
    return std::string(CL("\x1b[90m"))+l+rep(m,INNER+2)+rr+CL("\x1b[0m")+"\n";
}
static std::string padr(const std::string& s,int w){
    std::string o=s; int v=vis_len(s); if(v<w) o.append(w-v,' '); return o;
}
static const char* MODE_COL[4]={"\x1b[36m","\x1b[35m","\x1b[33m","\x1b[32m"};

struct Snap {
    double el=0; u64 tested=0; double speed=0;
    std::vector<double> tsp; std::vector<Found> found;
};
static std::string build_frame(Run& r,const Snap& s){
    std::string f;
    const TargetSet& ts=*r.ts;
    long double total=ldexpl(1.0L,r.bits-1);
    long double pct=100.0L*s.tested/total; if(pct>100) pct=100;
    double avg=s.tested/(s.el>0?s.el:1e-9);
    long double eta=(total-s.tested)/(avg>0?avg:1);
    char b[256];

    f+=border("╔","═","╗");
    f+=row(std::string(CL("\x1b[1m\x1b[36m"))+"PUZZLE BITCOIN · secp256k1 · recherche multi-cœurs"+CL("\x1b[0m"));
    f+=border("╠","═","╣");
    double mb=(ts.bloom.size()*8.0+ts.list.size()*sizeof(Ent))/1048576.0;
    snprintf(b,sizeof b,"Cibles  : %s %s  (filtre + liste : %.1f Mo)",fmt_int(ts.list.size()).c_str(),ts.addr?"adresse(s)":"clé(s) publique(s)",mb);
    f+=row(b);
    snprintf(b,sizeof b,"Bits    : %d   Blocs : %s × 2^%d clés   Cœurs : %d",r.bits,fmt_int(r.NB).c_str(),r.bsize,r.nthreads);
    f+=row(b);
    f+=row("Plage   : "+short_hex(r.start)+"  →  "+short_hex(r.end));
    f+=border("╠","═","╣");
    int shown=std::min(r.nthreads,12);
    for(int i=0;i<shown;i++){
        int m=r.st[i].mode.load(); u64 blk=r.st[i].block.load();
        std::string mn=(m>=0)?MODE_NAME[m]:"terminé";
        std::string col=(m>=0&&g_ansi)?MODE_COL[m]:"";
        U256 bs=r.start; add_raw(bs,bs,shl_u64(blk,r.bsize));
        snprintf(b,sizeof b,"C%-2d ",i+1);
        std::string line=b+col+padr(mn,12)+CL("\x1b[0m")+" ";
        snprintf(b,sizeof b,"bloc %9s  ",m>=0?fmt_int(blk).c_str():"-");
        line+=b;
        line+=padr(m>=0?short_hex(bs):"-",24);
        snprintf(b,sizeof b,"%6.2f Mk/s",s.tsp[i]/1e6);
        line+=b;
        f+=row(line);
    }
    if(r.nthreads>shown){ snprintf(b,sizeof b,"… +%d autres cœurs",r.nthreads-shown); f+=row(CL("\x1b[90m")+std::string(b)+CL("\x1b[0m")); }
    f+=border("╠","═","╣");
    int W=40; int fl=(int)(pct/100.0L*W+0.0001L); if(fl>W) fl=W;
    snprintf(b,sizeof b,"  %6.2Lf %%",pct);
    f+=row(std::string(CL("\x1b[32m"))+rep("█",fl)+CL("\x1b[90m")+rep("░",W-fl)+CL("\x1b[0m")+b);
    snprintf(b,sizeof b,"Testé   : %-12s Vitesse : %.2f Mk/s",fmt_keys((long double)s.tested).c_str(),s.speed/1e6);
    f+=row(b);
    snprintf(b,sizeof b,"Écoulé  : %-12s Reste   : ~%s",fmt_time(s.el).c_str(),fmt_time(eta).c_str());
    f+=row(b);
    snprintf(b,sizeof b,"Trouvées: %zu / %s",s.found.size(),fmt_int(ts.list.size()).c_str());
    f+=row(std::string(s.found.empty()?"":CL("\x1b[1m\x1b[32m"))+b+CL("\x1b[0m"));
    f+=border("╠","═","╣");
    int fstart=std::max(0,(int)s.found.size()-3);
    for(int i=0;i<3;i++){
        int idx=fstart+i;
        if(idx>=0&&idx<(int)s.found.size()){
            const Found& fd=s.found[idx];
            std::string pk=ent_text(ts,fd.ent); pk=pk.substr(0,10)+"…"+pk.substr(pk.size()-6);
            f+=row(std::string(CL("\x1b[32m"))+"★ "+CL("\x1b[0m")+pk+"  →  "+short_hex(fd.key));
        } else f+=row(i==0&&s.found.empty()?std::string(CL("\x1b[90m"))+"(aucune clé trouvée pour l'instant)"+CL("\x1b[0m"):"");
    }
    f+=border("╚","═","╝");
    return f;
}

static void run_engine(Run& r,bool display){
    r.t0=clk::now();
    int n=r.nthreads;
    std::vector<WArg> args(n);
    for(int i=0;i<n;i++){ args[i].r=&r; args[i].tid=i; }
#ifdef _WIN32
    std::vector<HANDLE> hs(n);
    for(int i=0;i<n;i++) hs[i]=CreateThread(NULL,0,thread_main,&args[i],0,NULL);
#else
    std::vector<std::thread> ths;
    for(int i=0;i<n;i++) ths.emplace_back(worker,&args[i]);
#endif
    std::vector<u64> prevk(n,0); double prevt=0; int prevLines=0;
    auto draw=[&](bool final_){
        double el=std::chrono::duration<double>(clk::now()-r.t0).count();
        Snap s; s.el=el; s.tsp.assign(n,0.0);
        double dt=el-prevt; if(dt<=0) dt=1e-9;
        for(int i=0;i<n;i++){
            u64 k=r.st[i].keys.load(); s.tsp[i]=(k-prevk[i])/dt; prevk[i]=k; s.tested+=k;
        }
        prevt=el; s.speed=s.tested/(el>0?el:1e-9);
        r.lock.lock(); s.found=r.found; r.lock.unlock();
        if(g_ansi){
            std::string f=build_frame(r,s);
            std::string out;
            if(prevLines>0){ char c[16]; snprintf(c,sizeof c,"\x1b[%dA",prevLines); out+=c; }
            out+=f; fputs(out.c_str(),stdout); fflush(stdout);
            prevLines=(int)std::count(f.begin(),f.end(),'\n');
        } else if(!final_){
            long double total=ldexpl(1.0L,r.bits-1);
            printf("\r[%6.2Lf%%] %.2f Mk/s | écoulé %s | trouvées %zu/%zu   ",
                100.0L*s.tested/total,s.speed/1e6,fmt_time(el).c_str(),s.found.size(),r.ts->list.size());
            fflush(stdout);
        }
    };
    if(display&&g_ansi){ fputs("\x1b[?25l",stdout); }
    if(display) draw(false);
    auto tp=clk::now();
    while(r.done.load()<n){
        sleep_ms(display?100:2);
        if(g_sigint.load()) r.stop.store(true);
        if(display&&std::chrono::duration<double>(clk::now()-tp).count()>=0.5){ tp=clk::now(); draw(false); }
    }
#ifdef _WIN32
    for(int i=0;i<n;i++){ WaitForSingleObject(hs[i],INFINITE); CloseHandle(hs[i]); }
#else
    for(auto& t:ths) t.join();
#endif
    if(display){
        draw(true);
        if(g_ansi) fputs("\x1b[?25h",stdout); else fputs("\n",stdout);
        fflush(stdout);
    }
}

// ---------------------------------------------------------------- initialisation & auto-tests
static void init_curve(){
    parse_hex(GX_HEX,GEN.x); parse_hex(GY_HEX,GEN.y);
    GEN.inf=false;
}

static bool engine_test(int bits,const std::vector<u64>& keys,const std::vector<u64>& expect,int nthreads,bool addr=false){
    TargetSet ts; ts.addr=addr;
    for(u64 k:keys){ U256 kk={{k,0,0,0}}; Aff P=aff_mul(kk,GEN); ts.list.push_back(ent_of_point(addr,P)); }
    finalize_targets(ts);
    Run r; init_run(r,bits,nthreads,&ts,false);
    run_engine(r,false);
    if(r.found.size()!=expect.size()) return false;
    for(u64 k:expect){
        bool ok=false;
        for(const Found& f:r.found) if(f.key.d[0]==k&&!f.key.d[1]&&!f.key.d[2]&&!f.key.d[3]) ok=true;
        if(!ok) return false;
    }
    return true;
}

static bool self_test(){
    bool ok=true;
    auto check=[&](bool c,const char* name){ if(!c){ fprintf(stderr,"AUTO-TEST ÉCHEC : %s\n",name); ok=false; } };
    check(on_curve(GEN),"G sur la courbe");
    U256 ex;
    Aff g2=aff_mul({{2,0,0,0}},GEN); parse_hex("C6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5",ex);
    check(eq(g2.x,ex),"2G");
    Aff g3=aff_mul({{3,0,0,0}},GEN); parse_hex("F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",ex);
    check(eq(g3.x,ex),"3G");
    U256 ks[4]={{{0xDEADBEEFCAFEBABEULL,0x0123456789ABCDEFULL,0x1111222233334444ULL,0x0ABCDEF012345678ULL}},
                {{0xFFFFFFFFFFFFFFFFULL,0,0,0}},{{0,1,0,0}},{{12345,0,0xABCDULL,0}}};
    for(int i=0;i<4;i++){
        Aff a=aff_mul(ks[i],GEN), j=jac_to_aff(jac_mul(ks[i],GEN));
        check(eq(a.x,j.x)&&eq(a.y,j.y)&&on_curve(a),"affine == jacobien");
    }
    build_tables();
    for(int i=1;i<=HALF;i++){
        Aff j=jac_to_aff(jac_mul({{(u64)i,0,0,0}},GEN));
        if(!(eq(j.x,gx[i])&&eq(j.y,gy[i]))){ check(false,"table i*G"); break; }
    }
    Aff ng=jac_to_aff(jac_mul({{(u64)(2*HALF),0,0,0}},GEN));
    check(eq(ng.x,SST.x)&&eq(ng.y,SST.y),"pas 2*HALF*G");

    // arithmétique : carré dédié, inversion par chaîne, hash160 par paquets
    {
        Rng g; g.seed(777); int bad=0;
        for(int n=0;n<4000;n++){
            U256 a; for(int i=0;i<4;i++) a.d[i]=g.next();
            if(n%5==1){ a=PRIME; a.d[0]-=g.next()%3000; }
            if(n%7==2){ a=ZERO; a.d[0]=g.next()%5; }
            if(geq(a,PRIME)) sub_raw(a,a,PRIME);
            U256 s1,s2; fe_sqr(s1,a); fe_mul(s2,a,a); if(!eq(s1,s2)) bad++;
            if(n%40==0&&!is_zero(a)){
                U256 inv=fe_inv(a),pr; fe_mul(pr,inv,a); if(!eq(pr,ONE)) bad++;
                U256 e=PRIME; e.d[0]-=2; if(!eq(inv,fe_pow(a,e))) bad++;
            }
        }
        check(bad==0,"carré / inversion");
        int bh=0;
        for(int n=0;n<200;n++){
            U256 xs[VLANES],hs[VLANES]; u64 ps[VLANES];
            for(int l=0;l<VLANES;l++){ for(int i=0;i<4;i++) xs[l].d[i]=g.next(); ps[l]=g.next()&1; }
            hash160_vec(xs,ps,hs);
            for(int l=0;l<VLANES;l++) if(!eq(hs[l],hash160_fast(xs[l],ps[l]))) bh++;
        }
        check(bh==0,"hash160 par paquets");
    }
    // SHA-256 / RIPEMD-160 / adresses (vecteurs connus : clé privée 1)
    {
        unsigned char pb[33],h[20]; pub33(GEN.x,GEN.y.d[0]&1,pb);
        hash160_bytes(pb,33,h);
        U256 want; parse_hex("00000000751e76e8199196d454941c45d1b3a323f1433bd6",want);
        unsigned char wb[20]={0x75,0x1e,0x76,0xe8,0x19,0x91,0x96,0xd4,0x54,0x94,0x1c,0x45,0xd1,0xb3,0xa3,0x23,0xf1,0x43,0x3b,0xd6};
        check(memcmp(h,wb,20)==0,"hash160(G) octets");
        check(eq(hash160_fast(GEN.x,GEN.y.d[0]&1),pack20(wb)),"hash160(G) rapide");
        check(eq(hash160_fast(g2.x,g2.y.d[0]&1),hash160_point_bytes(g2)),"hash160 rapide == octets (2G)");
        check(eq(hash160_fast(g3.x,g3.y.d[0]&1),hash160_point_bytes(g3)),"hash160 rapide == octets (3G)");
        (void)want;
        Ent e; e.x=pack20(wb); e.par=0;
        check(ent_addr_legacy(e)=="1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH","encodage Base58Check");
        check(ent_addr_bech32(e)=="bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4","encodage Bech32");
        Ent d1,d2,d3; 
        check(parse_address("1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH",d1)==1&&eq(d1.x,e.x),"décodage Base58Check");
        check(parse_address("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4",d2)==1&&eq(d2.x,e.x),"décodage Bech32 (majuscules)");
        check(parse_address("1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMI",d3)==0,"checksum Base58 invalide");
        check(parse_address("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5",d3)==0,"checksum Bech32 invalide");
        check(parse_address("3J98t1WpEZ73CNmQviecrnyiWrnqRhWNLy",d3)==2,"P2SH non supporté");
        check(parse_address("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0",d3)==2,"Taproot non supporté");
    }
    // lecture de texte : doublons, lignes invalides, CRLF, majuscules
    {
        Aff p1=aff_mul({{5,0,0,0}},GEN), p2=aff_mul({{77,0,0,0}},GEN);
        std::string a=compress_hex(p1), b=compress_hex(p2), A=a;
        for(auto& c:A) if(c>='a'&&c<='f') c-=32;
        std::string txt=a+"\r\n\r\n"+A+"\n"+b+" # commentaire\nzzzz\n"+std::string("04")+a.substr(2)+"\n"+a.substr(0,66-1)+"\n";
        TargetSet ts; u64 l,rj,dp,un; parse_targets_text(txt,ts,false,l,rj,dp,un);
        check(ts.list.size()==2&&dp==1&&rj==3&&l==6,"lecture du fichier texte");
        // aller-retour du fichier .bloom
        ts.src_hash=12345;
        const char* tmp="selftest.tmp.bloom";
        if(save_bloom(ts,tmp)){
            TargetSet t2; std::string err;
            bool lo=load_bloom(tmp,t2,err);
            check(lo&&t2.list.size()==2&&t2.src_hash==12345&&t2.nblocks==ts.nblocks,"relecture .bloom");
            if(lo) check(ts_has_exact(t2,p1.x,p1.y.d[0]&1)&&ts_has_exact(t2,p2.x,p2.y.d[0]&1)&&!ts_has_x(t2,g2.x),"contenu .bloom");
            // corruption volontaire : doit être détectée
            FILE* f=fopen(tmp,"r+b");
            if(f){ fseek(f,-3,SEEK_END); int c=fgetc(f); fseek(f,-3,SEEK_END); fputc(c^0x55,f); fclose(f);
                   TargetSet t3; std::string e2; check(!load_bloom(tmp,t3,e2),"détection de corruption"); }
            remove(tmp);
        }
    }
    // recherches complètes sur des clés connues (cas dégénérés, multi-cibles, multi-threads)
    check(engine_test(1,{1},{1},1),"bits=1");
    check(engine_test(2,{3},{3},1),"bits=2");
    check(engine_test(3,{4,7,5},{4,7,5},2),"bits=3");
    check(engine_test(7,{100},{100},1),"bits=7");
    check(engine_test(10,{700,600,1000,5},{700,600,1000},1),"bits=10 multi-cibles (1 thread)");
    check(engine_test(10,{700,600,1000,5},{700,600,1000},4),"bits=10 multi-cibles (4 threads)");
    check(engine_test(11,{1031,2047},{1031,2047},3),"bits=11");
    check(engine_test(17,{70000,66000,131071},{70000,66000,131071},4),"bits=17");
    check(engine_test(20,{0xFFFFF,0x80000,0x9ABCD},{0xFFFFF,0x80000,0x9ABCD},4),"bits=20");
    check(engine_test(22,{3000001},{3000001},2),"bits=22");
    check(engine_test(16,{12345},{},1),"clé absente de la plage");
    {   // clés aux frontières des lots de 2*HALF clés (début, milieu, fin, lot suivant)
        std::vector<u64> ek; for(u64 o:{0,1,HALF-1,HALF,HALF+1,2*HALF-1,2*HALF,2*HALF+1,3*HALF,1000,2047}) ek.push_back(2048+o);
        check(engine_test(12,ek,ek,1),"frontières de lots (clé publique)");
        check(engine_test(12,ek,ek,3,true),"frontières de lots (adresse)");
        std::vector<u64> e2; for(u64 o:{0,255,256,511,512,100000,262143}) e2.push_back(262144+o);
        check(engine_test(19,e2,e2,2),"frontières de lots, bloc plus grand");
        check(engine_test(19,e2,e2,2,true),"frontières de lots, bloc plus grand (adresse)");
    }
    check(engine_test(10,{700,600,1000,5},{700,600,1000},1,true),"adresses bits=10 (1 thread)");
    check(engine_test(14,{9000,12000,16383,300},{9000,12000,16383},4,true),"adresses bits=14 (4 threads)");
    check(engine_test(2,{3},{3},1,true),"adresses bits=2");
    return ok;
}

static bool looks_like_pub(const std::string& s){
    return s.size()==66&&s[0]=='0'&&(s[1]=='2'||s[1]=='3');
}
static std::string lower(std::string s){ for(auto& c:s) if(c>='A'&&c<='Z') c+=32; return s; }

static void usage(const char* prog){
    fprintf(stderr,
        "Usage : %s <cible> <bits> [address] [threads]\n"
        "  <cible> : clé publique compressée, adresse, fichier .txt (une cible par ligne) ou fichier .bloom\n"
        "  address : à ajouter quand les cibles sont des adresses Bitcoin (1... ou bc1q...)\n"
        "  --genpub <clé_privée_hex> | --genaddr <clé_privée_hex> : utilitaires de test\n",prog);
}

int main(int argc,char** argv){
#ifdef _WIN32
    SetConsoleOutputCP(65001);   // accents corrects dans cmd.exe
    { HANDLE h=GetStdHandle(STD_OUTPUT_HANDLE); DWORD m=0;
      if(GetConsoleMode(h,&m)&&SetConsoleMode(h,m|0x0004)) g_ansi=true; }   // couleurs ANSI (Windows 10+)
#else
    g_ansi=isatty(1)||getenv("PUZZLE_ANSI");
#endif
    init_curve();
    if(argc==3 && (std::string(argv[1])=="--genpub"||std::string(argv[1])=="--genaddr")){
        U256 k; if(!parse_hex(argv[2],k)||is_zero(k)){ fprintf(stderr,"Clé invalide\n"); return 1; }
        Aff P=aff_mul(k,GEN);
        if(std::string(argv[1])=="--genpub") printf("%s\n",compress_hex(P).c_str());
        else { Ent e=ent_of_point(true,P); printf("%s\n%s\n",ent_addr_legacy(e).c_str(),ent_addr_bech32(e).c_str()); }
        return 0;
    }
    if(argc<3||argc>5){ usage(argv[0]); return 1; }
    std::string arg=argv[1];
    char* endp; long bits=strtol(argv[2],&endp,10);
    if(*endp||bits<1||bits>255){ fprintf(stderr,"Nombre de bits invalide (1 à 255).\n"); return 1; }
    bool addrmode=false; int nthreads=hw_threads();
    for(int i=3;i<argc;i++){
        std::string o=lower(argv[i]);
        if(o=="address") addrmode=true;
        else if(!o.empty()&&o.find_first_not_of("0123456789")==std::string::npos) nthreads=atoi(o.c_str());
        else { fprintf(stderr,"Argument inconnu : %s\n",argv[i]); usage(argv[0]); return 1; }
    }

    // ---- chargement des cibles
    TargetSet ts; ts.addr=addrmode;
    Ent single;
    bool is_single_pub=!addrmode&&looks_like_pub(arg)&&parse_pub(arg,single);
    int addr_rc=addrmode?parse_address(arg,single):0;
    if(!addrmode&&looks_like_pub(arg)&&!is_single_pub){ fprintf(stderr,"Clé publique invalide ou hors de la courbe secp256k1.\n"); return 1; }
    if(is_single_pub||(addrmode&&addr_rc==1)){
        ts.list.push_back(single); finalize_targets(ts);
        if(addrmode) printf("Cible unique : %s  (hash160 %s)\n",ent_addr_legacy(single).c_str(),ent_hash_hex(single).c_str());
        else printf("Cible unique : %s\n",ent_hex(single).c_str());
    } else if(addrmode&&addr_rc==2){
        fprintf(stderr,"Adresse valide mais non supportée (seules les adresses P2PKH '1...' et P2WPKH 'bc1q...' le sont).\n"); return 1;
    } else {
        bool isbloom=arg.size()>=6&&arg.substr(arg.size()-6)==".bloom";
        if(isbloom){
            std::string err; TargetSet tmp;
            if(!load_bloom(arg,tmp,err)){ fprintf(stderr,"Impossible de charger %s : %s\n",arg.c_str(),err.c_str()); return 1; }
            if(tmp.addr!=addrmode){
                fprintf(stderr,tmp.addr?"Ce filtre contient des adresses : ajoute l'argument address.\n"
                                       :"Ce filtre contient des clés publiques : retire l'argument address.\n");
                return 1;
            }
            ts=tmp;
            printf("Filtre chargé : %s  (%s %s)\n",arg.c_str(),fmt_int(ts.list.size()).c_str(),ts.addr?"adresses":"clés publiques");
        } else {
            std::string txt;
            if(!read_file(arg,txt)){
                if(!addrmode&&(parse_address(arg,single)!=0))
                    fprintf(stderr,"Cette cible est une adresse Bitcoin : ajoute l'argument address.\n");
                else fprintf(stderr,"Impossible de lire %s (ni clé publique, ni adresse, ni fichier valide).\n",arg.c_str());
                return 1;
            }
            u64 h=fnv64(txt);
            size_t dot=arg.find_last_of('.'), slash=arg.find_last_of("/\\");
            std::string bname=((dot==std::string::npos||(slash!=std::string::npos&&dot<slash))?arg:arg.substr(0,dot))+".bloom";
            std::string err; TargetSet old;
            if(load_bloom(bname,old,err)&&old.src_hash==h&&old.addr==addrmode){
                ts=old; printf("Filtre existant réutilisé : %s  (%s cibles)\n",bname.c_str(),fmt_int(ts.list.size()).c_str());
            } else {
                u64 lines,rej,dups,unsup; parse_targets_text(txt,ts,addrmode,lines,rej,dups,unsup); ts.src_hash=h;
                if(ts.list.empty()){
                    fprintf(stderr,"Aucune cible valide dans %s (%s lignes lues).%s\n",arg.c_str(),fmt_int(lines).c_str(),
                        addrmode?"":" Si ce sont des adresses, ajoute l'argument address.");
                    return 1;
                }
                printf("Fichier lu : %s lignes, %s valides, %s doublons, %s rejetées",
                    fmt_int(lines).c_str(),fmt_int(ts.list.size()).c_str(),fmt_int(dups).c_str(),fmt_int(rej).c_str());
                if(unsup) printf(", %s non supportées (P2SH/P2WSH/Taproot)",fmt_int(unsup).c_str());
                printf("\n");
                if(save_bloom(ts,bname)) printf("Filtre enregistré : %s\n",bname.c_str());
                else fprintf(stderr,"Attention : impossible d'écrire %s\n",bname.c_str());
            }
        }
    }

    printf("Auto-tests en cours... "); fflush(stdout);
    if(!self_test()){ printf("ÉCHEC\n"); return 2; }
    printf("OK\n");

    if(nthreads<1) nthreads=1;
    if(nthreads>64) nthreads=64;

    signal(SIGINT,on_sigint);
    Run run; init_run(run,(int)bits,nthreads,&ts,true);
    run_engine(run,true);

    // ---- récapitulatif
    double el=std::chrono::duration<double>(clk::now()-run.t0).count();
    bool interrupted=g_sigint.load();
    printf("\n");
    for(const Found& f:run.found){
        if(ts.addr)
            printf("  ✔ %s  /  %s\n      clé publique : %s\n",ent_addr_legacy(f.ent).c_str(),ent_addr_bech32(f.ent).c_str(),f.pub.c_str());
        else printf("  ✔ %s\n",f.pub.c_str());
        printf("      clé privée   : %s\n      décimal      : %s\n",to_hex(f.key).c_str(),to_dec(f.key).c_str());
    }
    printf("\n%zu / %zu cible(s) trouvée(s) en %s%s.\n",run.found.size(),ts.list.size(),fmt_time(el).c_str(),interrupted?" (interrompu)":"");
    if(!run.found.empty()) printf("Résultats enregistrés dans cle_trouvee.txt\n");
    return run.found.size()==ts.list.size()?0:(interrupted?130:1);
}
