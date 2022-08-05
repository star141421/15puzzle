/*
        generator a 6-6-3 additive pattern database and run IDA*

    F : The tiles(or space) in locations, 4bits each
        tile '1','2','15','space' -> 0x0,0x1,0xe,0xf
        lowest 4bits of f -> tile at upper left
    G : The locations of considering tiles, 4bits each
        upper_left, upper_right, bottom_right -> 0x0, 0x3, 0xf
        lowest 4bit of g -> location of smallest tile considered(maybe tile '1')
    P : The location of 'space' (F>>(P*4) == 0xf)
*/

#include <conio.h>

#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <random>
#include <vector>

using namespace std;

using u64 = uint64_t;
using u32 = uint32_t;
using u16 = uint16_t;
using u8 = uint8_t;

// The tiles in locations when 15puzzle is SOLVED.
const u64 ac = 0xfedcba9876543210ull;

void output(u64 f) {
  for (int i = 0; i < 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      printf("%02llu ", (f + 1) & 15);
      f >>= 4;
    }
    printf("\n\n");
  }
}

constexpr u64 ftog(u64 f) {
  u64 g = 0;
  f >>= 2;
  for (u64 i = 1; i < 16; ++i) {
    g |= (i << (f & 60));
    f >>= 4;
  }
  return g;
}

const int dr_up = -16, dr_down = 16, dr_left = -4, dr_right = 4;

// p not going out of range
inline bool dr_valid(int p, int dr) {
  if (dr < 0) return p & (-dr * 3);
  return (~p) & (dr * 3);
}

u64 movef(u64 f, int p, int dr) {
  if (dr == -16) return ((~(15ull << p) | (f << 16)) & f) | (15ull << (p - 16));
  if (dr == -4) return ((~(15ull << p) | (f << 4)) & f) | (15ull << (p - 4));
  if (dr == 4) return ((~(15ull << p) | (f >> 4)) & f) | (15ull << (p + 4));
  if (dr == 16) return ((~(15ull << p) | (f >> 16)) & f) | (15ull << (p + 16));
  return 0ull;
}

// value of 'space' is not required before move, while not set after move!!
inline u64 movef_fast(u64 f, int p, int dr) {
  if (dr < 0) return (((f << -dr) ^ f) & (15ull << p)) ^ f;
  if (dr > 0) return (((f >> dr) ^ f) & (15ull << p)) ^ f;
  return 0ull;
}

void radix_sort24(u64* a, u64* b, int len) {
  int sum[4096] = {}, sum1[4096] = {};
  for (int i = 0; i < len; ++i) {
    ++sum[a[i] & 4095];
    ++sum1[(a[i] >> 12) & 4095];
  }
  for (int q = 1; q < 4096; ++q) {
    sum[q] += sum[q - 1];
    sum1[q] += sum1[q - 1];
  }
  for (int q = len - 1; q >= 0; --q) {
    b[--sum[a[q] & 4095]] = a[q];
  }
  for (int q = len - 1; q >= 0; --q) {
    a[--sum1[(b[q] >> 12) & 4095]] = b[q];
  }
}

u8 MEM[0xfede00 * 5];

/*
1 3 3 3
1 1 2 2
1 1 2 2
1 2 2 0     partition 1 is symmetric

use template to generate difference efficient code for different parts.
*/
template <int PART_ID>
class db {
 public:
  static u8 at(u32 part_g) { return m()[part_g]; };
  static void fillM() {
    for (int i = 0; i < m_size(); ++i) m32()[i] = (255u << 24);
    vector<u64> ds, ns;
    try_push(ds, gstart(), 0, 32u << 18, gspace(gstart()));
    u32 cur = 1u;
    u32 ts = 0, maxds = 0;
    while (ds.size()) {
      ts += ds.size();
      do_layer(std::ref(ns), std::ref(ds), (cur << 24) | 0xffffffu);
      ++cur;
      ds.resize(ns.size());
      maxds = max(maxds, (u32)ns.size());
      radix_sort24(&ns[0], &ds[0], ds.size());
      swap(ns, ds);
      ns.clear();
      size_t j = 0;
      for (size_t i = 0; i < ds.size(); ++i) {
        if (i == 0 || u32(ds[i]) != u32(ds[j - 1])){
          ds[j++] = ds[i];
        } else {
          ds[j - 1] |= ds[i];
        }
      }
      ds.resize(j);
    }
    cout << ts << " " << maxds << endl;
    for (int i = 0; i < m_size(); ++i) m()[i] = (m32()[i] >> 24);
  }

 private:
  static constexpr int m_size() { return PART_ID != 3 ? 0xfedd00 : 4096; }
    static constexpr u8* m() { return MEM + (PART_ID - 1)*0xfedd00; }
  static constexpr u32* m32() { return (u32*)m(); };
  static constexpr u32 gstart() {
    return PART_ID == 1 ? 0xc98540u : (PART_ID == 2 ? 0xedba76u : 0x321u);
  }
  static constexpr int tile_count() { return PART_ID == 3 ? 3 : 6; };

  static void try_push(vector<u64>& V, u32 g, u32 cur, u32 r, u32 space) {
    if ((m32()[g] & r) == 0) {
      u32 r1;
      do {
        r1 = r;
        r = (r | (r << 1) | (r >> 1) | (r << 5) | (r >> 5)) & space;
      } while (r1 != r);
      m32()[g] |= r;
      if (m32()[g] & 0x80000000u) m32()[g] &= cur;
      V.push_back((u64(r) << 32) | g);
      // partition 1 is symmetric, deal with g to save time
      if (PART_ID == 1) {
        g = (g >> 20) | ((g << 20) & 0xf00000) | ((g >> 8) & 0xff0) |
            ((g << 8) & 0xff000);
        r = (r >> 10) | (r << 10);
        r = ((r & (15u * 1025 * 32)) << 5) | ((r & (15u * 1025 * 1024)) >> 5);
        g ^= 0xcccccc;
        if (m32()[g] & 0x80000000u) m32()[g] &= cur;
        m32()[g] |= r;
      }
    }
  }

  static u32 gspace(u32 g) {
    u32 space = 0b111101111011110111100000u;
    for (int i = 0; i < tile_count() * 4; i += 4) {
      u32 z = ((g >> i) & 15u);
      space -= (32u << (z + (z >> 2)));
    }
    return space;
  }
  static void do_layer(vector<u64>& nxt, const vector<u64>& doing, u32 cur) {
    for (u64 gr : doing) {
      u32 g = gr;
      u32 r = (gr >> 32);  // tiles can be reached from f, 16+3bit(gap between
                           // line), with 5bit shift
      u32 space = gspace(g);
      for (int i = 0; i < tile_count() * 4; i += 4) {
        u32 gi = (g >> i) & 15;
        gi += (gi >> 2);
        u32 f1 = r >> gi;
        gi = (32u << gi);
        u32 s1 = space ^ gi;
        if (f1 & 1u) {
          try_push(nxt, g - (4u << i), cur, gi, s1 ^ (gi >> 5));
        }
        if (f1 & 16u) {
          try_push(nxt, g - (1u << i), cur, gi, s1 ^ (gi >> 1));
        }
        if (f1 & 64u) {
          try_push(nxt, g + (1u << i), cur, gi, s1 ^ (gi << 1));
        }
        if (f1 & 1024u) {
          try_push(nxt, g + (4u << i), cur, gi, s1 ^ (gi << 5));
        }
      }
    }
  }
};

// sort by low 24 bit, *b is used as buffer
void init() {
  db<1>::fillM();
  db<2>::fillM();
  db<3>::fillM();
}

u64 deep_transpose(u64 f_or_g) {
  u64 g = f_or_g;
  u64 t = (g ^ (g >> 24)) & 0xff00ff00;
  g = g ^ t ^ (t << 24);
  t = (g ^ (g >> 12)) & 0x0000f0f00000f0f0ull;
  g = g ^ t ^ (t << 12);
  return ((g & 0x3333333333333333ull) << 2) |
         ((g & 0xccccccccccccccccull) >> 2);
}

constexpr int g123map[15] = {0,     12 * 4, 13 * 4, 14 * 4, 1 * 4,
                             2 * 4, 6 * 4,  7 * 4,  3 * 4,  4 * 4,
                             8 * 4, 9 * 4,  5 * 4,  10 * 4, 11 * 4};

template <int dr>
constexpr u64 editg123(u64 g123, u32 x) {
  return g123 - (int64_t{dr / 4} << g123map[x]);
}
template <int dr>
constexpr u64 editgx(u64 gx, u32 x) {
  x = 15u & ((x << 2) | (x >> 2));
  return gx - ((16ll / dr) << g123map[x]);
}
int h_of_g123(u64 g123) noexcept {
  return int(db<1>::at(g123 & 0xffffff)) + db<2>::at((g123 >> 24) & 0xffffff) +
         db<3>::at(g123 >> 48);
}
int h_of_g(u64 g) noexcept {
  u64 g123 = 0;
  for (int i = 0; i < 15; ++i) g123 += (((g >> (4 * i)) & 15ull) << g123map[i]);
  return h_of_g123(g123);
}

int ida_route[96];
int ida_ri;
u64 ida_count;

template <int last_dr>
bool ida_dfs_v2(u64 f, int p, int lim, u64 g123, u64 gx) {
  g123 = editg123<last_dr>(g123, (f >> (p + last_dr)) & 15u);
  if (h_of_g123(g123) > lim) return false;
  gx = editgx<last_dr>(gx, (f >> (p + last_dr)) & 15u);
  if (h_of_g123(gx) > lim) return false;
  ida_route[lim] = last_dr;
  if (h_of_g123(gx) == 0) return true;

  f = movef_fast(f, p, last_dr);
  p += last_dr;
  //++ida_count;
  --lim;
#define IDA_DFS(DR)                                       \
  if (dr_valid(p, DR)) {                                  \
    if (ida_dfs_v2<DR>(f, p, lim, g123, gx)) return true; \
  }
  IDA_DFS(last_dr);
  IDA_DFS(64 / last_dr);
  IDA_DFS(-64 / last_dr);
  return false;
}

bool ida_dfs_starter(u64 f, int lim) {
  --lim;
  int p = 0;
  for (int i = 0; i < 16; ++i) {
    if ((15ull & (f >> (i * 4))) == 15ull) p = i * 4;
  }
  u64 g123 = 0ull, gx = 0ull;
  u64 g = ftog(f);  //((ftog(f)<<4)>>4);
  for (int i = 0; i < 15; ++i) g123 += (((g >> (4 * i)) & 15ull) << g123map[i]);
  g = deep_transpose(g);
  for (int i = 0; i < 15; ++i) gx += (((g >> (4 * i)) & 15ull) << g123map[i]);

  IDA_DFS(dr_down);
  IDA_DFS(dr_right);
  IDA_DFS(dr_left);
  IDA_DFS(dr_up);
#undef IDA_DFS
  return false;
}

void ida(u64 f) {
  int lim = h_of_g(ftog(f));
  ida_count = 0;
  for (; lim < 99; lim += 2) {
    if (ida_dfs_starter(f, lim)) break;
    //cout<<lim<<endl;
  }
  ida_ri = lim;
  std::reverse(ida_route, ida_route + lim);
  // cout<<"total ida_dfs call "<<ida_count<<endl;
}

u64 myrand() {
  static default_random_engine generator;
  static uniform_int_distribution<u64> distribution(0ull, -1ull);
  return distribution(generator);
}

u64 randF() {
  u64 f = 0;
  vector<int> v{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
  int inv;
  do {
    std::random_shuffle(v.begin(), v.end());
    inv = 0;
    for (int i = 0; i < 16; ++i) {
      if (v[i] == 15) {
        inv += i / 4;
        continue;
      }
      for (int j = i + 1; j < 16; ++j) {
        if (v[i] > v[j]) ++inv;
      }
    }
  } while ((inv & 1) == 0);
  for (int i = 0; i < 16; ++i) {
    f |= (u64(v[i]) << i * 4);
  }
  int p = 0;
  for (int i = 0; i < 16; ++i) {
    if ((15ull & (f >> (i * 4))) == 15ull) p = i * 4;
  }
  for(int i=0;i<256;++i){
    int drs[4]={dr_up,dr_down,dr_left,dr_right};
    int dr=drs[rand()%4];
    if(dr_valid(p,dr)){
      f=movef(f,p,dr);
      p+=dr;
    }
  }
  return f;
}

namespace interface {

const int IMPORT = 128, RANDF = 129, FAIL = 130, NEXTI = 131, ILLACT = 132,
          EXIT = 133;

inline int conv(char act) {
  if (act == '2' || act == 's') return dr_down;
  if (act == '8' || act == 'w') return dr_up;
  if (act == '4' || act == 'a') return dr_left;
  if (act == '6' || act == 'd') return dr_right;
  if (act == 'r' || act == '0') return RANDF;
  if (act == 'h' || act == '1') return NEXTI;
  if (act == 'i' || act == '3') return IMPORT;
  if (act == 'q' || act == '9') return EXIT;
  return ILLACT;
}

bool act(u64& f, int act) {
  int p = 0;
  for (int i = 0; i < 16; ++i) {
    if ((15ull & (f >> (i * 4))) == 15ull) p = i * 4;
  }
#define DO_ACT(DR)                    \
  if (act == DR && dr_valid(p, DR)) { \
    f = movef(f, p, DR);              \
    return true;                      \
  }
  DO_ACT(dr_down);
  DO_ACT(dr_right);
  DO_ACT(dr_left);
  DO_ACT(dr_up);
#undef DO_ACT
  return false;
}
void clrscr() { system("cls"); }

void interact() {
  cout << "interact start" << endl;
  getche();
  u64 now = ac;
  while (1) {
    clrscr();
    output(now);
    fflush(stdout);
    int op = conv(getche());
    if (op == RANDF) {
      now = randF();
    } else if (op == NEXTI && now != ac) {
      auto t = clock();
      ida(now);
      auto t1 = clock();
      double gap = double(t1 - t);
      cout << "depth= " << ida_ri << "  time= " << gap << endl;
      getche();
      act(now, ida_route[0]);
    } else if (op == IMPORT) {
      now = 0;
      for (int i = 0; i < 16; ++i) {
        u32 in;
        cin >> in;
        clrscr();
        now |= (((u64)(in - 1) & 15) << i * 4);
        output(now);
        fflush(stdout);
      }
    } else if (op == EXIT) {
      exit(0);
    } else {
      act(now, op);
    }
  }
}

}  // namespace interface

int main() {
  auto t = clock();
  init();
  auto t1 = clock();
  cout << "fillM cost " << (t1 - t) << endl;
  double avgd=0.0,avgr=0.0;
  vector<u64> v(10000);
  for(int i=0;i<10000;++i) v[i]=randF();
  t1 = clock();
  for(int i=0;i<10000;++i){
      ida(v[i]);
      avgr+=ida_ri;
  }
  auto t2 = clock()-t1;
  cout<<"average heuristic value "<<avgd/1e3<<endl;
  cout<<"average solution value "<<avgr/1e3<<endl;
  cout<<"solution cost "<<t2<<endl;
  interface::interact();
}
/* 80 step cases, time in ms (AMD Ryzen 7 5800H 3.20 GHz)
 0 12 9 13 15 11 10 14 3 7 2 5 4 8 6 1    6679
 0 12 10 13 15 11 14 9 3 7 2 5 4 8 6 1    6659
 0 11 9 13 12 15 10 14 3 7 6 2 4 8 5 1    17317
 0 15 9 13 11 12 10 14 3 7 6 2 4 8 5 1    17437
 0 12 9 13 15 11 10 14 3 7 6 2 4 8 5 1    6805
 0 12 14 13 15 11 9 10 3 7 6 2 4 8 5 1    5447
 0 12 10 13 15 11 14 9 3 7 6 2 4 8 5 1    5361
 0 12 11 13 15 14 10 9 3 7 6 2 4 8 5 1    6963
 0 12 10 13 15 11 9 14 7 3 6 2 4 8 5 1    8209
 0 12 9 13 15 11 14 10 3 8 6 2 4 7 5 1    6268
 0 12 9 13 15 11 10 14 8 3 6 2 4 7 5 1    5141
 0 12 14 13 15 11 9 10 8 3 6 2 4 7 5 1    3589
 0 12 9 13 15 11 10 14 7 8 6 2 4 3 5 1    5275
 0 12 10 13 15 11 14 9 7 8 6 2 4 3 5 1    3693
 0 12 9 13 15 11 10 14 3 7 5 6 4 8 2 1    9295
 0 12 9 13 15 11 10 14 7 8 5 6 4 3 2 1    6510

 */
