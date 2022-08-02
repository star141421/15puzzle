#include <bits/stdc++.h>
#include <thread>

using namespace std;

using u64 = uint64_t;
using u32 = uint32_t;
using u16 = uint16_t;
using u8 = uint8_t;

constexpr u64 base(u8 p){
    return 15ull<<p;
}
constexpr u64 rbase(u8 p){
    return ~(15ull<<p);
}
const u64 ac = 0xfedcba9876543210ull;

const u8 dr_up=-16, dr_down=16, dr_left=-4, dr_right=4;

constexpr u8 rev(u8 dr){
    return -dr;
}

template<u8 dr>
inline bool dr_valid(u8 p){
    if(dr&128) return p&u8(u8(-dr)*3u);
    return (~p)&u8(dr*3u);
}
template<u8 dr>
inline u64 moved_dr(u64 f,u8 p){
    //static_assert(dr<=u8(16) || u8(-dr)<=u8(16));
    if(dr==u8(-16)) return ((rbase(p)|(f<<16))&f)|base(p-16);
    if(dr==u8(-4)) return ((rbase(p)|(f<<4))&f)|base(p-4);
    if(dr==u8(16)) return ((rbase(p)|(f>>16))&f)|base(p+16);
    if(dr==u8(4)) return ((rbase(p)|(f>>4))&f)|base(p+4);
    //assert(0);
    return 114514ull;
}
constexpr u64 trans(u64 f){
    u64 g=0;
    f>>=2;
    for(u64 i=1;i<16;++i){
        g |= (i<<(f&60));
        f>>=4;
    }
    return g;
}
constexpr u32 encode8(u32 g){
    u32 r= g&15;
    const u64 _1x16=0x1111111111111110ull;
    u64 bsum = ac-(_1x16<<(r*4));
    g>>=2;
    for(u32 i=15;i>8;--i){
        r = r*i + ((bsum>>(g&60))&15);
        bsum -= (_1x16<<(g&60));
        g>>=4;
    }
    return r;
}
constexpr int encode7(u32 g){
    int r= g&15;
    const u64 _1x16=0x1111111111111110ull;
    u64 bsum = ac-(_1x16<<(r*4));
    g>>=2;
    for(int i=15;i>9;--i){
        r = r*i + ((bsum>>(g&60))&15);
        bsum -= (_1x16<<(g&60));
        g>>=4;
    }
    return r;
}
u8 M8[518918400], M7[57657600];

template<int S>
inline void Vpush(vector<u32>& V,u32 g,u8 cur){
    int e = (S==8) ? encode8(g) : encode7(g);
    if(S==8){
        if(M8[e]==u8(255)){
            M8[e]=cur;
            V.push_back(g);
        }
    }else{
        if(M7[e]==u8(255)){
            M7[e]=cur;
            V.push_back(g);
        }
    }
    
}
template<int S>
void twork(vector<u32>& nxt,const vector<u32>& doing, u8 cur){
    for(u32 g : doing){
        u32 f=0;
        for(int i=0;i<S*4;i+=4){
            f|=(1u<<((g>>i)&15u));
        }
        for(int i=0;i<S*4;i+=4){
            u8 p=(g>>i)&15;
            if(dr_valid<u8(-4)>(p) && ((f>>(p-4))&1)==0){
                Vpush<S>(nxt,g-(4u<<i),cur);
            }
            if(dr_valid<u8(-1)>(p) && ((f>>(p-1))&1)==0){
                Vpush<S>(nxt,g-(1u<<i),cur);
            }
            if(dr_valid<u8(1)>(p) && ((f>>(p+1))&1)==0){
                Vpush<S>(nxt,g+(1u<<i),cur);
            }
            if(dr_valid<u8(4)>(p) && ((f>>(p+4))&1)==0){
                Vpush<S>(nxt,g+(4u<<i),cur);
            }
        }
    }
}
template<int S>
void fillM_mt(){
    const int thread_count = 16;
    auto t=chrono::high_resolution_clock::now();
    if(S==8) memset(M8,255,sizeof(M8));
    else memset(M7,255,sizeof(M7));
    u32 gs= S==8 ? 0x76543210 : 0x0edcba98;
    vector<u32> ds[thread_count], ns[thread_count];
    Vpush<S>(ds[0],gs,0);
    u8 cur=1;
    u32 total_sz=1;
    while(total_sz){
        vector<thread> pool(thread_count);
        for(int i=0;i<thread_count; ++i){
            pool[i]=thread(twork<S>,std::ref(ns[i]),std::ref(ds[i]), cur);
        }
        for(int i=0;i<thread_count; ++i) pool[i].join();
        //balance work between threads
        total_sz=0;
        for(int i=0;i<thread_count; ++i) ds[i].resize(0);
        for(int i=0;i<thread_count; ++i){
            total_sz+=ns[i].size();
            swap(ds[i], ns[i]);
        }
        u32 target_sz=total_sz/thread_count;
        for(int i=0, j=0;i<thread_count && j<thread_count;){
            while(j<thread_count && ds[j].size() >= target_sz) ++j;
            while(i<thread_count && ds[i].size() <= target_sz+1) ++i;
            if(i<thread_count && j<thread_count){
                u32 move_sz = min(target_sz-ds[j].size(), ds[i].size()-target_sz-1);
                int z1 = ds[j].size(), z2=ds[i].size()-move_sz;
                ds[j].resize(z1+move_sz);
                for(u32 k=0;k<move_sz;++k) ds[j][z1+k] = ds[i][z2+k];
                ds[i].resize(z2);
            }
        }
        auto t1 = chrono::high_resolution_clock::now();
        cout<<int(cur)<<" "<<total_sz<<" time "<< (chrono::duration<double>(t1-t)).count()<<endl;
        ++cur;
    }
}

//IDA*
u8 h_of_g(u64 g) noexcept{
    u32 e8 = encode8(u32(g)), e7 = encode7(g>>32);
    u8 r1 =M8[e8] + M7[e7];
    /*
    0 A 0 A    0 0 A A
    B 0 B 0    0 0 A A
    0 A 0 A    B B 0 0
    B 0 B 0    B B 0 0
    */
    g = ((g&0x0f0f00000f0f0000ull)>>12)|((g&0x0000f0f00000f0f0ull)<<12)|(g&0xf0f00f0ff0f00f0full);
    g = ((g&0x00ff00ff00000000ull)>>24)|((g&0x00000000ff00ff00ull)<<24)|(g&0xff00ff0000ff00ffull);
    g = ((g&0x3333333333333333ull)<<2)|((g&0xccccccccccccccccull)>>2);
    e8 = encode8(u32(g));
    e7 = encode7(g>>32);
    u8 r2 =M8[e8] + M7[e7];
    return r1<r2 ? r2 : r1;
}

void output(u64 o) {
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      printf("%02llu ", (o + 1) & 15);
      o >>= 4;
    }
    printf("\n\n");
  }
}

vector<u8> ida_route;
bool ida_dfs(u64 f,u64 g,u8 cur,u8 lim,u8 p,u8 last_dr){
    //cout<<"p= "<<int(p)<<endl;
    //output(f);
    //getchar();
    if(f==ac) return true;
    if(cur+h_of_g(g)>=lim) return false;
    ++cur;
    #define DO(DR)\
    if(last_dr != u8(-DR) && dr_valid<DR>(p)){\
        u64 f1 = moved_dr<DR>(f,p);\
        u8 p1=p+DR;\
        u64 g1 = g + ((int64_t(-int8_t(DR))/4)<<(4*((f>>p1)&15)));\
        ida_route.push_back(DR);\
        if(ida_dfs(f1,g1,cur,lim,p1,DR)) return true;\
        ida_route.pop_back();\
    }
    DO(dr_up);
    DO(dr_down);
    DO(dr_left);
    DO(dr_right);
    return false;
}

void ida(u64 f){
    u64 g=trans(f);
    u8 p=0;
    for(int i=0;i<16;++i){
        if((15ull&(f>>(i*4)))==15ull) p=i*4;
    }
    ida_route.clear();
    for(u8 i=1;i<99;i+=2){
        if(ida_dfs(f,g,0u,i,p,0)) break;
        cout<<"ida done "<<int(i)<<endl;
    }
}


u64 myrand(){
    static default_random_engine generator;
    static uniform_int_distribution<u64> distribution(0ULL,518918400);
    return distribution(generator);
}

int main(){
    fillM_mt<8>();
    fillM_mt<7>();
    
    while(1){
        u64 now=0;
        for(int i=0;i<16;++i){
            u32 in;
    		scanf("%d",&in);
    		now|=((u64(in-1)&15)<<i*4);
        }
        cout<<int(h_of_g(trans(now)))<<endl;
        ida(now);
        cout<<ida_route.size()<<endl;
    }
}
