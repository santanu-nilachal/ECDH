// asiacrypt_u64.c  --  Asiacrypt lattice search (ns,sns,alpha,beta,dim,bound)
// Scan ranges: 1 <= d < n, 0 <= t <= 2d-1
// n-tight: C(n,2) cap via least_m_binom_ge_dim0 (k = 2)
// 64-bit combinatorics with overflow guards; long double for bounds.

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <math.h>

// ------------------------ small helpers ------------------------
static inline uint64_t u64_min(uint64_t a, uint64_t b){ return a < b ? a : b; }
static inline bool add_u64(uint64_t a, uint64_t b, uint64_t* out){
    if (UINT64_MAX - a < b) return false; *out = a + b; return true;
}

// gcd for uint64
static uint64_t gcd_u64(uint64_t a, uint64_t b){
    while (b){ uint64_t t = a % b; a = b; b = t; }
    return a;
}

// gcd for (__int128) a and uint64 b
static uint64_t gcd_u128_u64(__int128 a, uint64_t b){
    if (b == 0) return (uint64_t)a;
    while (b){
        uint64_t r = (uint64_t)(a % b);
        a = b; b = r;
    }
    return (uint64_t)a;
}

// ------------------------ binomial (exact, 64-bit if fits) ------------------------
static bool binom_u64(uint64_t n, uint64_t k, uint64_t* out){
    if (k > n){ *out = 0; return true; }
    if (k == 0 || k == n){ *out = 1; return true; }
    if (k > n - k) k = n - k;
    __int128 res = 1;
    for (uint64_t i = 1; i <= k; ++i){
        __int128 num = res * (__int128)(n - k + i);
        __int128 val = num / (__int128)i; // exact division
        if (val > (__int128)UINT64_MAX) return false;
        res = val;
    }
    *out = (uint64_t)res;
    return true;
}

// ------------------------ ns, sns (64-bit) ------------------------
static bool ns_u64(uint64_t n, uint64_t d, uint64_t* out){
    uint64_t s = 0, term;
    uint64_t up = d > n ? n : d;
    for (uint64_t k = 0; k <= up; ++k){
        if (!binom_u64(n,k,&term)) return false;
        if (!add_u64(s,term,&s)) return false;
    }
    *out = s; return true;
}

static bool sns_u64(uint64_t n, uint64_t d, uint64_t* out){
    uint64_t s = 0, term;
    uint64_t up = d > n ? n : d;
    for (uint64_t k = 0; k <= up; ++k){
        if (!binom_u64(n,k,&term)) return false;
        __int128 prod = (__int128)k * (__int128)term;
        if (prod > (__int128)UINT64_MAX) return false;
        uint64_t add = (uint64_t)prod;
        if (!add_u64(s,add,&s)) return false;
    }
    *out = s; return true;
}

// ------------------------ dim, alpha, beta, bound (ASIACRYPT) ------------------------
// dim(n,d,t)   = (t+1)*C(n,d+1) + 2*d*ns(n,d)
static bool dim_asiacrypt_u64(uint64_t n, uint64_t d, uint64_t t, uint64_t* out){
    uint64_t c, ns;
    if (!binom_u64(n, d+1, &c)) return false;
    if (!ns_u64(n, d, &ns))     return false;
    __int128 lhs = (__int128)(t + 1) * (__int128)c;
    __int128 rhs = (__int128)(2 * d) * (__int128)ns;
    __int128 sum = lhs + rhs;
    if (sum > (__int128)UINT64_MAX) return false;
    *out = (uint64_t)sum; return true;
}

// alpha(n,d,t)=((2d+t+2)(t+1)/2)*C(n,d+1)+ d(2d-1)*ns(n,d)+ 2d*sns(n,d)
static bool alpha_asiacrypt_ld(uint64_t n, uint64_t d, uint64_t t, long double* out){
    uint64_t c, ns, sns;
    if (!binom_u64(n, d+1, &c)) return false;
    if (!ns_u64(n, d, &ns))     return false;
    if (!sns_u64(n, d, &sns))   return false;

    long double A = (long double)(2*d + t + 2);
    long double B = (long double)(t + 1);
    long double term1 = (A * B / 2.0L) * (long double)c;
    long double term2 = (long double)d * (long double)(2*d - 1) * (long double)ns;
    long double term3 = (long double)(2*d) * (long double)sns;

    *out = term1 + term2 + term3;
    return isfinite(*out);
}

// beta(n,d,t) = 2*d*d*ns(n,d) - (2*d-2)*sns(n,d)
static bool beta_asiacrypt_ld(uint64_t n, uint64_t d, long double* out){
    uint64_t ns, sns;
    if (!ns_u64(n, d, &ns))   return false;
    if (!sns_u64(n, d, &sns)) return false;

    long double term1 = (long double)(2 * d) * (long double)d * (long double)ns;
    long double term2 = (long double)(2 * d - 2) * (long double)sns;

    *out = term1 - term2;
    return isfinite(*out);
}

// bound(n,d,t) = (d*(dim - n) - beta) / alpha
static bool bound_asiacrypt_ld(uint64_t n, uint64_t d, uint64_t t, long double* out){
    uint64_t w;
    long double alpha, beta;
    if (!dim_asiacrypt_u64(n,d,t,&w))      return false;
    if (!alpha_asiacrypt_ld(n,d,t,&alpha)) return false;
    if (!beta_asiacrypt_ld(n,d,&beta))     return false;

    long double num = (long double)d * ((long double)w - (long double)n) - beta;
    if (!(isfinite(alpha) && fabsl(alpha) > 0.0L && isfinite(num))) return false;
    *out = num / alpha;
    return isfinite(*out);
}

// ------------------------ binomial threshold: C(m,k) >= dim0 ------------------------
static bool binom_ge_threshold(uint64_t n, uint64_t k, uint64_t threshold){
    if (k == 0) return 1 >= threshold;
    if (k > n)  return (0 >= threshold);
    if (k > n - k) k = n - k;

    __int128 res = 1;
    __int128 TH  = (__int128)threshold;

    for (uint64_t i = 1; i <= k; ++i){
        uint64_t num = n - k + i;
        uint64_t den = i;

        uint64_t g = gcd_u64(num, den);
        num /= g; den /= g;

        if (den > 1){
            uint64_t g2 = gcd_u128_u64(res, den);
            res /= g2; den /= g2;
        }
        if (res >= TH) return true;
        if (num != 0 && res > ((__int128)((~(unsigned __int128)0) >> 1)) / (__int128)num)
            return true;
        res *= (__int128)num;
        if (res >= TH) return true;
    }
    return (res >= TH);
}

static uint64_t least_m_binom_ge_dim0(uint64_t dim0, uint64_t k){
    if (k == 0) return 0;
    if (dim0 <= 1) return k;
    if (k == 1)   return dim0;

    uint64_t lo = k, hi = k;
    while (!binom_ge_threshold(hi, k, dim0)){
        if (hi > UINT64_MAX/2) break;
        hi <<= 1;
    }
    while (lo < hi){
        uint64_t mid = lo + ((hi - lo) >> 1);
        if (binom_ge_threshold(mid, k, dim0)) hi = mid;
        else lo = mid + 1;
    }
    return lo;
}

// ------------------------ main ------------------------
int main(void){
    const long double tau = 0.45L;
    const long double Snd = 1.0L - tau;
    const uint64_t T = 7000;

    uint64_t n0=0, d0=0, t0=0;
    uint64_t dim0 = UINT64_MAX;
    long double bestB = -1.0L;

    // -------- Phase 1: seed search (Asiacrypt ranges) --------
    for (uint64_t n = 1; n <= T; ++n){
        for (uint64_t d = 1; d < n; ++d){                 // 1 <= d < n
            uint64_t dim_d0;
            if (!dim_asiacrypt_u64(n,d,0,&dim_d0)) break; // overflow / not representable
            if (dim_d0 > dim0) break;                     // monotone in t => early out on d if t=0 already too big

            uint64_t tmax = 2*d;                          // t = 0 .. 2d-1
            for (uint64_t t = 0; t < tmax; ++t){
                uint64_t w;
                if (!dim_asiacrypt_u64(n,d,t,&w)) break;
                if (w > dim0) break;                      // dim increases with t

                long double b;
                if (!bound_asiacrypt_ld(n,d,t,&b)) continue;
                if (b >= Snd && w < dim0){
                    n0=n; d0=d; t0=t; dim0=w; bestB=b;
                    printf("found (phase1): n=%" PRIu64 " d=%" PRIu64 " t=%" PRIu64
                           "  bound=%.6Lf  dim=%" PRIu64 "\n", n,d,t,b,w);
                }
            }
        }
    }

    if (dim0 == UINT64_MAX){
        printf("No feasible triple under 64-bit range (try smaller T or bigger ints).\n");
        return 0;
    }

    // -------- Phase 2: n-tight via binomial cap C(n,2) (k = 2) --------
    uint64_t k = 2;
    uint64_t m_ge = least_m_binom_ge_dim0(dim0, k);
    uint64_t n_tight_raw = (m_ge > 0 ? m_ge - 1 : 0);
    printf("binomial threshold (k=%" PRIu64 "): m_ge=%" PRIu64 ", n_tight_raw=%" PRIu64 "\n",
           k, m_ge, n_tight_raw);

    uint64_t n_scan_max = (n_tight_raw > T ? T : n_tight_raw);
    printf("using scan cap T=%" PRIu64 " -> scanning n up to %" PRIu64 "\n", T, n_scan_max);

    bool improved = true;
    while (improved){
        improved = false;
        for (uint64_t n = 1; n <= n_scan_max; ++n){
            for (uint64_t d = 1; d < n; ++d){
                uint64_t dim_d0;
                if (!dim_asiacrypt_u64(n,d,0,&dim_d0)) break;
                if (dim_d0 > dim0) break;

                uint64_t tmax = 2*d;
                for (uint64_t t = 0; t < tmax; ++t){
                    uint64_t w;
                    if (!dim_asiacrypt_u64(n,d,t,&w)) break;
                    if (w > dim0) break;

                    long double b;
                    if (!bound_asiacrypt_ld(n,d,t,&b)) continue;
                    if (b >= Snd && w < dim0){
                        n0=n; d0=d; t0=t; dim0=w; bestB=b; improved = true;
                        printf("improve (phase2): n=%" PRIu64 " d=%" PRIu64 " t=%" PRIu64
                               "  bound=%.6Lf  dim=%" PRIu64 "\n", n,d,t,b,w);

                        m_ge = least_m_binom_ge_dim0(dim0, k);
                        n_tight_raw = (m_ge > 0 ? m_ge - 1 : 0);
                        n_scan_max = (n_tight_raw > T ? T : n_tight_raw);
                        printf("  -> threshold: m_ge=%" PRIu64 ", n_tight_raw=%" PRIu64
                               ", scanning up to %" PRIu64 "\n", m_ge, n_tight_raw, n_scan_max);
                        break;
                    }
                }
                if (improved) break;
            }
            if (improved) break;
        }
    }

    printf("\nBest triple: n=%" PRIu64 ", d=%" PRIu64 ", t=%" PRIu64
           " | bound=%.6Lf | dim=%" PRIu64 "\n", n0,d0,t0,bestB,dim0);
    return 0;
}

