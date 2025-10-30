#SageMath code for Elliptic Curve Hidden Number Problem when oracle returns few MSBs per call. 


import numpy as np

def Final_Lattice(G,I,L):
    I1 = []
    for i in range(2^n):
         for i0 in range(2*d,2*d+1+1):
              A = [i0]
              C = ZZ(i).digits(base = 2, padto = n)
              j = 0
              while(j <= n-1):
                   A.append(C[j])
                   j = j+1
              sum = 0
              for j in range(1,n+1):
                   sum = sum+A[j]
              if(sum <= d):
                   I1.append(A)
                   



    G_Tilde = [] 
    I2 = []
    INDEX = []
    
    for i in range(len(I)):
         if(I[i] in I1):
              continue
         else:
              if(I[i][0] <= t and L[i] == d+1):
                   I2.append(I[i])
                   INDEX.append(i)
                   continue
              G_Tilde.append(G[i])
           

    for i1 in range(len(I2)):
         POLY_SET = []
         VAR = []
         i = I2[i1][0]
         for j in range(1,n+1):
              if(I2[i1][j] == 1):
                   POLY_SET.append(F[j-1])
                   VAR.append(Z[j])
                
         l = 0
         for j in range(1,n+1):
                   l = l+I2[0][j]
           
         RING_2 = IntegerModRing(Prime^d)
         M = zero_matrix(RING_2, 2*l)

         POLY_TEMP = []
         LD_MON = []
         a = 1
         for j in range(len(VAR)):
              a = a*VAR[j]
         for j in range(2*l):
              LD_MON.append(a*x0^j)
         for v in range(2):
              f = 1
              for j1 in range(len(POLY_SET)):
                   f = x0^v
                   for j2 in range(len(POLY_SET)):
                        if(j1 == j2):
                             f = f*VAR[j2]
                        else:
                             f = f*POLY_SET[j2]
                   POLY_TEMP.append(f)
         for j1 in range(2*l):
              for j2 in range(2*l):
                   c = (POLY_TEMP[j1]).coefficient(LD_MON[j2])(ZERO)
                   M[j1,j2] = c
         M_inverse = M.inverse()

         g_tilde = G[INDEX[i1]]



         F1 = []
         i0 = I2[i1][0]
         for u in range(d+1 ):
              f = x0*ZZ(M_inverse[i0,d+u+1])
              f1 = x0^(2*d)
              for j1 in range(len(POLY_SET)):
                   if(j1 == u):
                        cij = (POLY_SET[j1]).coefficient(x0^2)
                        cij = cij(ZERO)
                        cij = ZZ(cij)
                        f = f*cij
                   else:
                        f = f*POLY_SET[j1]
                        f1 = f1*VAR[j1]
                                          
              F1.append(f1)
              g_tilde = g_tilde + f


         g_tilde_monomials = g_tilde.monomials()
         Temp = 0
         for u in range(len(g_tilde_monomials)):
              cu = g_tilde.coefficient(g_tilde_monomials[u])
              cu = cu(ZERO)
              cu = ZZ(cu)
              cu = cu%Prime^d
              cu = ZZ(cu)
              Temp = Temp+cu*g_tilde_monomials[u]

         g_tilde = Temp

         F11 = []
         for u in range(len(F1)):
              cij = g_tilde.coefficient(F1[u])
              cij = cij(ZERO)
              cij = ZZ(cij)
              F11.append(cij)

           


         g_tilde_1 = 0
         for u in range(d+1):
              f1 = 1
              for j1 in range(len(POLY_SET)):
                   if(j1 == u):
                        f1 = f1*F11[u]
                   else:
                        f1 = f1*POLY_SET[j1]

              g_tilde_1 = g_tilde_1 + f1
            


         g_tilde = g_tilde-g_tilde_1
         g_tilde_monomials = g_tilde.monomials()
         temp = 0
         for u in range(len(g_tilde_monomials)):
              cu = g_tilde.coefficient(g_tilde_monomials[u])
              cu = cu(ZERO)
              cu = ZZ(cu)
              cu = cu%Prime^d
              cu = ZZ(cu)
              temp = temp+cu*g_tilde_monomials[u]
         g_tilde = temp
         G_Tilde.append(g_tilde)

    return G_Tilde



def Solution(F):
    I = []
    S = []
    #Generating index set starts, S contains corresponding monomials
    for i in range(2^n):
         for i0 in range(2*d+1+1):
              A = [i0]
              C = ZZ(i).digits(base = 2, padto = n)
              j = 0
              while(j <= n-1):
                   A.append(C[j])
                   j = j+1
              sum = 0
              for j in range(1,n+1):
                   sum = sum+A[j]
              if(sum <= d):
                   I.append(A)
                   monomial = 1
                   for j in range(n+1):
                        monomial = monomial*Z[j]^A[j]
                   S.append(monomial)
    for i in range(2^n):
         for i0 in range(t+1):
              A = [i0]
              C = ZZ(i).digits(base = 2, padto = n)
              j = 0
              while(j <= n-1):
                   A.append(C[j])
                   j = j+1
              sum = 0
              for j in range(1,n+1):
                   sum = sum+A[j]
              if(sum == d+1):
                   I.append(A)
                   monomial = 1
                   for j in range(n+1):
                        monomial = monomial*Z[j]^A[j]
                   S.append(monomial)



    

    # Generating index set ends
    #G stores all polynomials for lattice construction
    G = []
    L = [] 
    for i in range(len(I)):
         l = 0
         for j in range(1,n+1):
              l = l+I[i][j]
         L.append(l)  
     
         i0 = I[i][0]
         if(l == 0):
              G.append(x0^i0*Prime^d)
         if(l == 1 and i0 <= 1):
              g = x0^i0*Prime^d
              for j in range(1,n+1):
                   g = g*Z[j]^I[i][j]
              G.append(g)
         if(l == 1 and i0 >= 2):
              g = x0^(i0-2)*Prime^(d-1)
              for j in range(1,n+1):
                   g = g*F[j-1]^I[i][j]
              G.append(g)
         if(l >= 2 and i0 >= 2*l):
              g=x0^(i0-2*l)*Prime^(d-l)
              for j in range(1,n+1):
                   g = g*F[j-1]^I[i][j]
              G.append(g)
         if(l >= 2 and i0<2*l):
              #Store polynomials in POLY_SET & variables in VAR
              POLY_SET = []
              VAR = []
              for j in range(1,n+1):
                   if(I[i][j] == 1):
                        POLY_SET.append(F[j-1])
                        VAR.append(Z[j])


              RING_2 = IntegerModRing(Prime^(l-1))
              M = zero_matrix(RING_2, 2*l)

              #Store polynomials in POLY_TEMP. After multiplying by suitable matrix monomials of LD_MON will be leading terms.
              POLY_TEMP = []
              LD_MON = [] 
              a = 1
              for j in range(len(VAR)):
                   a = a*VAR[j]
              for j in range(2*l):
                   LD_MON.append(a*x0^j)
              for v in range(2):
                   f = 1
                   for j1 in range(len(POLY_SET)):
                        f = x0^v
                        for j2 in range(len(POLY_SET)):
                             if(j1 == j2):
                                  f = f*VAR[j2]
                             else:
                                  f = f*POLY_SET[j2]
                        POLY_TEMP.append(f)
              for j1 in range(2*l):
                   for j2 in range(2*l):
                        c = (POLY_TEMP[j1]).coefficient(LD_MON[j2])(ZERO)
                        M[j1,j2] = c
              M_inverse = M.inverse()
              f = 0
              for j in range(2*l):
                   f = f+ZZ(M_inverse[i0,j])*(POLY_TEMP[j])
              g = 0
              for j in range(len(S)):
                   cij = (f.coefficient(S[j]))(ZERO)
                   cij = cij%Prime^(l-1)
                   g = g+cij*S[j]
              G.append(g*Prime^(d+1-l))
              #Polynomial generation ends

    G = Final_Lattice(G,I,L)

    

    S = []
    for i in range(len(G)):
        LD = Set((G[i]).monomials()).difference(Set(S))
        for j in range(len(LD)):
           S.append(LD[j])


    X = 2^(Unknown) #Upper bound of unknown is X

    #From polynomials of G, construct lattice which is generated by row vectors of M
    Lattice_dimension = len(S)
    #M is the matrix corresponding to shift polynomials
    M = zero_matrix(ZZ,Lattice_dimension)

    



    PT1 = [Z[i]*X for i in range(n+1)]
    PT2 = [X]*(n+1)

    for i in range(Lattice_dimension):
         f = G[i]
         f = f(PT1)
         for j in range(Lattice_dimension):
              cij = f.coefficient(S[j])
              cij = cij(ZERO)
              M[i,j] = cij

    #Store those polynomials which are zero over integers in POLY_SET
    POLY_SET = []
    time_lll = cputime()
    M = M.LLL()
    
    time_lll = cputime(time_lll)
    for i in range(Lattice_dimension): 
         f = 0
         for j in range(Lattice_dimension):
              f = f+(M[i][j]/S[j](PT2))*S[j]

         if(f(ROOT)==0):
              POLY_SET.append(f)
         else:
              break
    #Store primes in PRIME_SET. Over these prime fields, we calculate Grobner basis

    PRIME_SET, prod_prime, p = [], 1, 2
    while prod_prime <= 2*X:
     if is_prime(p):
        PRIME_SET.append(p); prod_prime *= p
     p += 1
     
    CRT = []
    time_gb = 0
    for PRIME in PRIME_SET:
         CRT_MOD = PolynomialRing(GF(PRIME), n+1, 'X')
         POLY_PRIME = []
         for l in range(len(POLY_SET)):
              POLY_PRIME.append(CRT_MOD(POLY_SET[l]))
         Iideal = (POLY_PRIME)*CRT_MOD
         tt = cputime()
         B = Iideal.groebner_basis()
         if(len(B)<n): #In this case our attack fails
                return[0,0,0,0,0]
         time_gb = time_gb+cputime(tt)
         TARGET_ROOT = ZZ(B[Target](ZERO))
         if(TARGET_ROOT<0):
             TARGET_ROOT = -TARGET_ROOT
         if(TARGET_ROOT>0):
             TARGET_ROOT = PRIME-TARGET_ROOT
         CRT.append(TARGET_ROOT)
    
    Y = crt(CRT,PRIME_SET)  #Use Chinese Remainder Theorem
    Y1 = Y-prod_prime #2nd Option of the target co-ordinate of root
    return[Y,Y1,time_lll,time_gb,Lattice_dimension]



PARA = [[6,1,1], [10,1,0], [5,2,1], [13,1,0], [6,2,0], [16,1,0], [7,2,0], [5,3,0], [5,3,1], [5,3,2], [21,1,0]]
Known = [[132,154,176,263,357],  [125,145,165,245,330],  [129,150,172,256,347],  [120,140,160,235,320],  [130,152,174,263,360], [116,135,155,230,310], [126,148,168,253,340],   [128,150,170,255,345],  [125,145,166,250,339], [124,144,165,247,335], [114,132,152,225,301]]
a = -3
for par in range(10): # Change lower and upper limit of par to change parameter
    n = PARA[par][0]
    d = PARA[par][1]
    t = PARA[par][2]
    print('n = ', n, ' \t d = ',d, '\t t = ',t)
    RING1 = PolynomialRing(QQ,n+1,['x%d'%(0)]+['y%d'%(i) for i in range(1,n+1)] )
    RING1.inject_variables()

    Z = list(RING1.gens())
    ZERO = [0]*(n+1)
    for ecc in range(1,6):
         if(ecc == 1):
              Prime =2^192-2^64-1
              b = int("0x64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1", 16)
              px = int("188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012",16)
              py = int("07192b95ffc8da78631011ed6b24cdd573f977a11e794811",16)
              BIT = 192
         if(ecc == 2):
              Prime = 26959946667150639794667015087019630673557916260026308143510066298881
              b = int("b4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4",16)
              px = int("b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21",16)
              py = int("bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34",16)
              BIT = 224
         if(ecc == 3):
              Prime = 2^256-2^224+2^192+2^96-1
              b = 41058363725152142129326129780047268409114441015993725554835256314039467401291
              px = int("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",16)
              py = int("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",16)
              BIT = 256
         if(ecc == 4):
              Prime = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
              b = int("0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",16)
              px = int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",16)
              py = int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f ",16)
              BIT = 384

         if(ecc == 5):
              Prime = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
              b = int("051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",16)
              px = int("c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",16)
              py = int("11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",16)
              BIT = 521
         suc = 0
         b = ZZ(b)
         E = EllipticCurve(GF(Prime),[0, 0, 0, a, b])
         P = E(px,py)
         Unknown = BIT-Known[par][ecc-1] #Unknown part from LSB side
         LLLT = []
         GBT = []
         h0 = floor(ZZ(P[0])/2^(Unknown))*2^Unknown
         e0 = ZZ(P[0])-h0
         for run in range(1,3+1):
              ROOT = [e0]
              F = []
              R = E.random_point()
              for i in range(n):
                   mi = ZZ.random_element(Prime)
                   Q = mi*R
                   R = P+Q
                   S = P-Q
                   h = ceil(ZZ(R[0])/2^(Unknown))*2^Unknown
                   e = ZZ(R[0])-h
                   hi = ceil(ZZ(S[0])/2^(Unknown))*2^Unknown
                   ei = ZZ(S[0])-hi

                   hb = h+hi
                   eb = e+ei
                   ROOT.append(eb)
                   Ai = ZZ((hb*(h0-Q[0])^2-2*h0^2*Q[0]-2*(a+Q[0]*Q[0])*h0-2*a*Q[0]-4*b)%Prime)
                   Bi = ZZ(2*(hb*(h0-Q[0])-2*h0*Q[0]-a-Q[0]*Q[0])%Prime)
                   Ci = ZZ((hb-2*Q[0])%Prime)
                   Di = ZZ(((h0-Q[0])^2)%Prime)
                   Ei = ZZ(2*(h0-Q[0])%Prime)
                   f_i = Ai+Bi*x0+Ci*x0^2+Di*Z[i+1]+Ei*x0*Z[i+1]+x0^2*Z[i+1]
                   F.append(f_i)

              Target = n #Target = 0 corresponds to e_0 and Target \in [1,n] corresponds to \widetilde{e}_i for i = 1,.., n

              SOL = Solution(F)
              if(SOL[0] == ROOT[Target] or SOL[1] == ROOT[Target]):
                   suc = suc+1
              else:
                   continue
              LLLT.append(SOL[2])
              GBT.append(SOL[3])
              print(f"Exp: {run}\t Success: {suc}\t Lattice Dimension: {SOL[4]}" f"\t Avg. LLL time: {np.mean(LLLT):0.2f}"
    f"\t Avg. GB time: {np.mean(GBT):0.2f}" f"\t Curve: NIST {Prime.nbits()}")

         print('++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++')

                                                      
