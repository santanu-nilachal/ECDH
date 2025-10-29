def ns(n,d):
   f=0
   for s in range(d+1):
      f=f+binomial(n,s)
   return f
   

def sns(n,d):
   f=0
   for s in range(d+1):
      f=f+s*binomial(n,s)
   return f
   
   
def dim(n,d):
   return (2*d+1)*ns(n,d)
   
def alpha(n,d):
   return d*(2*d+1)*ns(n,d) + (2*d+1)*sns(n,d)
   
   
def beta(n,d):
   return d*(2*d+1)*ns(n,d) - (2*d-1)*sns(n,d)
   
   
def bound(n,d):
   f=(d*dim(n,d)-beta(n,d)-d*n)/alpha(n,d)
   return f
   
   

tau = 0.55

Snd = 1 -tau

dim_0 = 2^1000
d0 = 0
T = 100
for n in range(1,T+1):
  for d in range(1,n):
     
     if(bound(n,d)>Snd and (dim(n,d)<dim_0)):
        dim_0 = dim(n,d)
        d0=d
        print(round(bound(n,d),4),n,d, dim_0)
        

n_tight = ceil(dim_0/3-1)


x = 1
while(bound(n_tight,x)<Snd):
   x += 1



from math import comb

def least_m_binom_ge_dim0(dim0: int, k: int) -> int:
    """
    Return the smallest m such that C(m, k) >= dim0.
    Assumes dim0 >= 1 and k >= 1.
    """
    if k <= 0:
        raise ValueError("k must be >= 1")
    if dim0 <= 1:
        return k  # C(k,k)=1 >= dim0

    # Fast path for k=1: C(m,1)=m
    if k == 1:
        return dim0

    # Lower/upper bracket: start at m=k, grow upper by doubling
    lo = k
    hi = k
    while comb(hi, k) < dim0:
        hi *= 2  # exponential growth to find a cap

    # Binary search in [lo, hi]
    while lo < hi:
        mid = (lo + hi) // 2
        if comb(mid, k) >= dim0:
            hi = mid
        else:
            lo = mid + 1
    return lo  # minimal m with C(m,k) >= dim0

# After you compute dim_0 and d_init:
m_ge = least_m_binom_ge_dim0(dim_0, x)
n_tight = m_ge - 1  


for n in range(1,T+1):
  for d in range(x,d0):
     
     if(bound(n,d)>Snd and (dim(n,d)<dim_0)):
        dim_0 = dim(n,d)
        d0=d
        print(round(bound(n,d),4),n,d, dim_0)

