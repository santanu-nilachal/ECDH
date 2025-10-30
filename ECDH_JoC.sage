def union(a, b):
    """
    Ordered union for Sage/Python sequences.
    Returns a list containing all unique items of `a` followed by any items in `b`
    that are not already present. Preserves the order of appearance.

    Works when elements are hashable (fast path) and also when they are not (fallback).
    """
    out = list(a)
    try:
        seen = set(a)  # fast path if elements are hashable
        for x in b:
            if x not in seen:
                out.append(x)
                seen.add(x)
    except TypeError:
        # fallback for unhashable elements (e.g., some Sage objects)
        for x in b:
            if x not in out:
                out.append(x)
    return out



import numpy as np

import subprocess
import time

def REDUCE(f,N):
         """
          Reduce polynomial f coeffs mod N by evaluating coeff polynomials at ZERO.
         Uses globals: ZERO.
         """
         
         MONO = f.monomials()
         g = 0
         for j in range(len(MONO)):
                            cj = f.coefficient(MONO[j])
                            cj = cj(ZERO)
                            cj = cj%(N)
                            cj = ZZ(cj)
                            g = g + cj*MONO[j]
         return g
         
 
 


         


def Function_L(A, summation):
                    """
                    Build helper polynomial with coeff of LD equal to 1 (Type-1/2 mix).
                    Uses globals: n, Z, H, B_SET, Prime, ZERO.
                    """
   
                    POLY_SET_INITIAL_1 = []
                    a = 1
                    for k in range(1,n+1):
                        a = a*Z[k+n]^A[k]
                    
                    LD = Z[0]^A[0]*a
                    #print('LD', LD)
                    VAR_TEMP = [a*Z[0]^j for j in range(2*summation)]
 

                    for u in range(2):
                     for j in range(1,n+1):
                        if(A[j]==0):
                           continue
                        f = Z[0]^u
                        for k in range(1,n+1):
                             if(A[k]==0):
                                  continue
                             if(k==j):
                                f=f*Z[k+n]^A[j]                                
                             else:
                                f=f*H[k-1]^A[j]
                        POLY_SET_INITIAL_1.append(f)

                   
                    POLY_SET_INITIAL_2 = []
                    POLY_SET = []
                    BB_SET = []
                    for j in range(1,n+1):
                       if(A[j] == 1):
                          POLY_SET.append(H[j-1])
                          BB_SET.append(B_SET[j-1])




                    BB=[]
                    for j1 in range(len(POLY_SET)):
                       f = POLY_SET[j1]
                       g = 0
                       for u in range(len(POLY_SET)):
                         if(u==j1):
                           continue
                         f1 = 1
                         for j2 in range(len(POLY_SET)):
                           if(j2==j1):
                              continue
                           if(j2 == u):
                             f1=f1*BB_SET[j2]
                            
                           else:
                             f1 = f1*POLY_SET[j2]
                            

                         g=g+f1
                       g=g*f 
                       BB.append(g)
 
                    
                    for j1 in range(len(BB)):
                        POLY_SET_INITIAL_2.append(BB[j1])

                    for u in range(summation):
                      POLY_SET_INITIAL_1[u+ summation] = POLY_SET_INITIAL_1[u+ summation] - POLY_SET_INITIAL_2[u]
                      POLY_SET_INITIAL_1[u+ summation] = REDUCE(POLY_SET_INITIAL_1[u+ summation], Prime^(summation-1))

                    
                    RING_2 = IntegerModRing(Prime^(summation-1))
                    M = zero_matrix(RING_2, 2*summation)
                    for j1 in range(2*summation):
                      for j2 in range(2*summation):
                          c = (POLY_SET_INITIAL_1[j1]).coefficient(VAR_TEMP[j2])(ZERO)
                          M[j1,j2] = c

                    M_inverse = M.inverse() 
                    M_inverse = M_inverse.apply_map(ZZ)
                    #for j1 in range(2*summation):
                         #for j2 in range(2*summation):
                           #M_inverse[j1,j2] = ZZ(M_inverse[j1,j2])  

                             
                    for i0 in range(2*summation): 
            
                       f = sum((ZZ(M_inverse[i0,j]))*(POLY_SET_INITIAL_1[j]) for j in range(2*summation))
                       f = REDUCE(f,Prime^(summation-1)) 

                       
                       if(f.coefficient(LD)==1):
                            return f
                    
    


def Lattice(F,H, use_sage_lll=False):
    """
    Build triangular/helpful lattice; LLL via flatter (fallback Sage LLL);
    then CRT to recover the root coordinate.
    Returns [Y, Y1, time_lll, time_gb] or 0 on failure.
    Uses globals: n, d, t, Z, DD, BACK, ROOT, Prime, ZERO, Unknown, B_SET.
    """   

    
    L = []
    G_Tilde  = []
    LD = []
    #Generating index set starts, S contains corresponding monomials
    for i in range(2^n):
        for i0 in range(2*d-1):
            
            
            C = ZZ(i).digits(base = 2, padto = n)
            A = [C[j] for j in range(n)]            
            A.append(i0)
            A.reverse()
            summation = sum(A[j] for j in range(1, n+1))
            

            
            if(summation > d):
                continue

            ss = prod(Z[j]^A[j] for j in range(n+1))
            LD.append(ss)


            if(summation == 0):
                G_Tilde.append(Prime^d*Z[0]^i0)
                
               
                

            if(summation == 1):
                if(i0<2*summation):
                    f=1
                    for j in range(n+1):
                       f = f*Z[j]^A[j]
                    f = f*Prime^d
                if(i0>=2*summation):
                    f = Prime^(d-1)*Z[0]^(i0-2*summation)
                    #f=x0^(i0-2*summation)
                    for j in range(1,n+1):
                       f = f*F[j-1]^A[j]
                    
                      
                G_Tilde.append(f)



            if(summation >= 2 and summation <= d):
                
                if(i0<2*summation):
                    f = Prime^(d - summation +1)
                    g = Function_L(A, summation)

                    L.append([A, g])
                    f = f*g 
                                  


                if(i0>=2*summation):
                    f = Prime^(d-summation)*Z[0]^(i0-2*summation)
                    for j in range(1,n+1):
                       f = f*H[j-1]^A[j]
                    
                      
                G_Tilde.append(f)


    #print(G_Tilde)
    GG = []
    LL = []
    LD1 = []
    for i in range(2^n):
        for i0 in range(t+1):
            
            
            C = ZZ(i).digits(base = 2, padto = n)
            A = [C[j] for j in range(n)]  
                     
            A.append(i0)
            A.reverse()
            summation = sum(A[j] for j in range(1, n+1))
            if(summation != d+1):
                continue 
            g = Function_L(A, summation)
            GG.append(g)
            LL.append([A, g])
            ss = 1
            for j in range(n+1):
              ss = ss*Z[j]^A[j]
            LD1.append(ss)

    #print(LL[200])
    #print(LD1)
    LD0 = LD[:]
    
    while(1):
     LD = LD0[:]
     for i in range(len(LL)):
        j=ZZ.random_element(len(LL))
        LL[i], LL[j] = LL[j], LL[i]
        LD1[i], LD1[j] = LD1[j], LD1[i]

     LD.extend(LD1)

     G_Tilde_Type_2 = []
     G_Tilde_Type_2_Initial = []
     nd=binomial(n,d)
     A_4 = 0
     MONOMIAL = []

     for i in range(len(L)):
             
           
            A = L[i][0]
            g = L[i][1]
            summation = sum(A[j] for j in range(1, n+1))
            if(summation == d):
               
                ss = Z[0]^(2*d-1)
                for j1 in range(1,n+1):
                   if(A[j1]==1):
                     ss = ss*Z[j1+n]
                if((ss in MONOMIAL)==False):
                   MONOMIAL.append(ss)


     for i in range(len(LL)):
             
           
            A = LL[i][0]
            g = LL[i][1]
            summation = sum(A[j] for j in range(1, n+1))
                        
            #Type 2 stars
            if(A[0]==0):
                  
                  A_4 = A_4 + 1
                  if(A_4 > nd):
                      break
                  G_Tilde_Type_2_Initial.append(g)
                  #print(g)
                  A1 = [j for j in range(1, n+1) if A[j] == 1]
                  C1 = list(Combinations(A1, d))
                  
                  for j1 in range(len(C1)):
                       A2 = [0]*(n+1)
                       k = 2*d - 1
                       while(k>=0):
                        #for k in range(2*d):
                        ss = Z[0]^k
                        for j2 in range(len(C1[j1])):
                             ss = ss*Z[C1[j1][j2]+n]
                             A2[C1[j1][j2]] = 1
                        c = g.coefficient(ss)
                        c = c(ZERO)
                        
                        A2[0] = k
                        dd=0
                        for j2 in range(len(L)):
                          if(L[j2][0]==A2):
                               dd=1
                               g = g - c*L[j2][1]                                
                        if(dd==0):
                            g1 = Function_L(A2, d)
                            g = g - c*g1
                            
                        k = k - 1

                  C2 = list(Combinations(A1,d-1))
                   
                  for j1 in range(len(C2)):
                       for k in range(2*d-2, 2*d-1):
                        ss = Z[0]^k
                        tt = 1
                        for j2 in range(len(C2[j1])):
                             ss = ss*Z[C2[j1][j2]+n]
                             tt = tt*H[C2[j1][j2]-1]
                        
                        c = g.coefficient(ss)
                        c = c(ZERO)
                        g = g - c*tt
                        
                  G_Tilde_Type_2.append(g)
                  #print(len(g.monomials()))

     RING_2 = IntegerModRing(Prime^d)
     M = zero_matrix(RING_2,nd,nd)

     for i in range(len(G_Tilde_Type_2_Initial)):
           f = G_Tilde_Type_2_Initial[i]
           for j in range(nd):
               cij = f.coefficient(MONOMIAL[j])
               cij = cij(ZERO)
               cij = ZZ(cij)
               M[i,j] = cij
     if(M.det()==0):
        #print(0)
        continue
     break             

   
    #M = zero_matrix(RING_2,nd,nd)
    #print("HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH")
    #AA=M.det()
    #print(AA)
    #print('++++++++++++++++++++++++++++++++++++++++++++++')
    
    if(M.det()==0):
        #print(0)
        return 0
    
    M_inverse = M.inverse() 
    for j1 in range(nd):
       for j2 in range(nd):
           M_inverse[j1,j2] = ZZ(M_inverse[j1,j2]) 

    POLYNOMIAL_TO_CREATE_TYPE_3=[]
    for i0 in range(nd):             
	
        f = sum((ZZ(M_inverse[i0,j]))*(G_Tilde_Type_2_Initial[j]) for j in range(nd))
        f = REDUCE(f,Prime^d) 
        POLYNOMIAL_TO_CREATE_TYPE_3.append(f)

    

    G_Tilde_Type_3_Initial = Set(GG).difference(G_Tilde_Type_2_Initial)
    #print(len(G_Tilde_Type_3_Initial))
    G_Tilde_Type_3 = []

    for i in range(len(G_Tilde_Type_3_Initial)):
         f = G_Tilde_Type_3_Initial[i]  
         for j in range(len(MONOMIAL)):
            cij = f.coefficient(MONOMIAL[j])
            cij = cij(ZERO)
            cij = ZZ(cij)
            f = f - cij*POLYNOMIAL_TO_CREATE_TYPE_3[j]
         f=REDUCE(f,Prime^d) 
         #print(f(ROOT)%Prime^d)
         MONS = f.monomials()
         G_Tilde_Type_3.append(f)
         
            
    SS = []
    #print('--------------------------------------')
    for i in range(len(G_Tilde_Type_3)):
       f = G_Tilde_Type_3[i]
       #print(f(ROOT)%Prime^d, i, 'Type 3')
       SS = union(SS,f.monomials())

    #print('--------------------------------------')
    for i in range(len(G_Tilde_Type_2)):
       G_Tilde_Type_2[i] = Prime*G_Tilde_Type_2[i]
       f = G_Tilde_Type_2[i]
       #print(f(ROOT)%Prime^d, i, 'Type 2')
       SS = union(SS,f.monomials())
    #print('----------------------------------------')
    for i in range(len(G_Tilde)):
       f = G_Tilde[i]
       #print(f(ROOT)%Prime^d, i, 'Type 1')
       SS = union(SS,f.monomials())
    
    #print(len(SS))


    #print(Prime)
    FINAL = []
    for i in range(len(G_Tilde)):
       f = G_Tilde[i]
       f = f(BACK)
       g = REDUCE(f, Prime^d)
       if(g!=0):
          FINAL.append(g)
       else:
          FINAL.append(f)  


    for i in range(len(G_Tilde_Type_2)):
       f = G_Tilde_Type_2[i]
       f = f(BACK)
       g = REDUCE(f, Prime^d)
       if(g!=0):
          FINAL.append(g)
       else:
          FINAL.append(f)      



    for i in range(len(G_Tilde_Type_3)):
       f = G_Tilde_Type_3[i]
       f = f(BACK)
       g = REDUCE(f, Prime^d)
       if(g!=0):
          FINAL.append(g)
       else:
          FINAL.append(f) 

    SS = []
    for i in range(len(FINAL)):
         #print(FINAL[i]) 
         SS = union(SS, (FINAL[i]).monomials())
         #print(" ")
    R2 = [[mono.degree(Z[j]) for j in range(n+1)] for mono in SS]
    R2.sort(key=lambda r: (sum(r), list(reversed(r))))
    SS = [prod(Z[j]^rj for j, rj in enumerate(r)) for r in R2]  # or small loop if no prod()

    
    X = next_prime(ZZ.random_element(2^(Unknown-1),2^(Unknown))) #Upper bound of unknown is X
    
    PT  = [Z[i]*X for i in range(2*n+1)]
    PT1 = [X]*(2*n+1)

    FINAL1 = []
    for i in range(len(SS)):
        for j in range(len(LD)):
            if(SS[i]==LD[j]):
                f = FINAL[j]
                f = f(PT)
                FINAL1.append(f)




    FINAL2 = []
    LD2 = []
    for i1 in range(1000):
     for i in range(len(FINAL1)):
      if((FINAL1[i] in FINAL2)==True):
         continue
      S1 = (FINAL1[i]).monomials()
      S2 = Set(S1).difference(Set(LD2))
      if(len(S2)==1):
         FINAL2.append(FINAL1[i])
         LD2.append(S2[0])
    

    
    SS = []
    FINAL1 = []
    for i in range(len(LD2)):
       SS.append(LD2[i])
       FINAL1.append(FINAL2[i])
    
     
    M=zero_matrix(ZZ,len(FINAL1))
    for i in range(len(FINAL1)):
        f = FINAL1[i]
        for j in range(len(FINAL1)):
              cij = f.coefficient(SS[j])
              cij = cij(ZERO)
              M[i,j] = cij
              
                 
        
    
    
    if use_sage_lll:
     # Use Sage's built-in LLL for the first three parameters
     start_time = time.perf_counter()
     M = M.LLL()
     time_lll = time.perf_counter() - start_time
     
    else: 
     input_file = "input.txt"
     output_file = "output.txt"
    
     with open(input_file, "w") as f:
        f.write("[")  
        for i, row in enumerate(M):
            f.write("[{}]".format(" ".join(map(str, row))))  
            if i < (M.nrows() - 1):
                f.write("\n ")  
        f.write("\n]\n")  
        
     #time_lll=cputime()
     start_time = time.perf_counter()
    
    
     try:
        subprocess.run(["flatter", input_file, output_file], check=True)
        #print(f"Command 'flatter {input_file} {output_file}' executed successfully.")
     except subprocess.CalledProcessError as e:
        print(f"Error occurred: {e}")
        
     time_lll = time.perf_counter() - start_time
     
     # Read the matrix from the file
     with open(output_file, "r") as f:
        lines = f.readlines()
    
     # Initialize an empty list for the matrix
     matrix_rows = []
    
     for line in lines:
        stripped_line = line.strip()  # Remove leading and trailing whitespace
        if stripped_line:  # Check if the line is not empty
            # Remove any outer brackets and extra spaces
            stripped_line = stripped_line.strip("[] ")
            # Split the row into numbers and filter out empty strings
            numbers = [int(num) for num in stripped_line.split() if num]
            if numbers:  # Ensure only non-empty lists are added
                matrix_rows.append(numbers)
    
     # Optionally, convert to a matrix (uncomment if needed)
     M = matrix(ZZ, matrix_rows)


    
     
    POLY_SET = []
    for i in range(len(FINAL1)): #Consider 1st POLY[par] vectors after lattice reduction
         #print(i)
         f=0
         for j in range(len(FINAL1)):
              f = f + (M[i][j]/SS[j](PT1))*SS[j] 
         if(f(ROOT)==0):
              POLY_SET.append(f)
              
         else:
              break
    

    PRIME_SET = []
    j = 0
    prod_prime = 1
    for i in range(1000):
         if(is_prime(i) == True):
              prod_prime = prod_prime*i
              PRIME_SET.append(i)
              j = j + 1
         if(prod_prime>2*X):
              break
    set_verbose(-1) 

    CRT = []
    time_gb = 0
    for i in range(j):
         PRIME = PRIME_SET[i]
         CRT_MOD = PolynomialRing(GF(PRIME), 2*n+1, 'X')
         POLY_PRIME = []
         for l in range(len(POLY_SET)):
              POLY_PRIME.append(CRT_MOD(POLY_SET[l]))
         I = (POLY_PRIME)*CRT_MOD
         tt = cputime()
         B = I.groebner_basis()
         if(len(B)<n): #In this case our attack fails
                return[0,0,0,0,0]
         time_gb = time_gb+cputime(tt)
         TARGET_ROOT = ZZ(B[0](ZERO))
         if(TARGET_ROOT<0):
             TARGET_ROOT = -TARGET_ROOT
         if(TARGET_ROOT>0):
             TARGET_ROOT = PRIME-TARGET_ROOT
         CRT.append(TARGET_ROOT)
    CRT = list(CRT)
    Y = crt(CRT,PRIME_SET)
    Y1 = Y-prod_prime #2nd Option of the target co-ordinate of root
    return[Y,Y1,time_lll,time_gb] 

    
PARA =[[6,2,1], [7,2,1], [8,2,1], [12,2,1], [13,2,1], [16,2,0], [17,2,0], [18,2,0], [19,2,0], [20,2,0]]  #18

KNOWN =[0.65, 0.62, 0.61, 287/521, 284/521, 279/521, 277/521, 274/521, 271/521, 269/521]
a = -3

primes = [2^192-2^64-1, 26959946667150639794667015087019630673557916260026308143510066298881, 2^256-2^224+2^192+2^96-1, 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319, 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151]

bs = [int("0x64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1", 16), int("b4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4",16), 41058363725152142129326129780047268409114441015993725554835256314039467401291, int("0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",16), int("051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",16) ]

X_Coordinates = [int("188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012",16), int("b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21",16), int("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",16), int("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",16), int("c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",16)]

Y_Coordinates = [ int("07192b95ffc8da78631011ed6b24cdd573f977a11e794811",16), int("bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34",16), int("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",16), int("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f ",16), int("11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",16)]

bits = [192, 224, 256, 384, 521]



         

for par in range(0,10): # Change lower and upper limit of par to change parameter
    n = PARA[par][0]
    d = PARA[par][1]
    t = PARA[par][2]
    print('n = ', n, ' \t d = ',d, '\t t = ',t)
    RING1 = PolynomialRing(QQ,2*n+1,['x%d'%(0)]+['y%d'%(i) for i in range(1,n+1)]+['z%d'%(i) for i in range(1,n+1)] )
    #RING1.inject_variables()
    Z = list(RING1.gens())
    dim =0
    for l in range(d+1):
       dim = dim + binomial(n,l)
    dim = dim*(2*d-1) + (t+1)*binomial(n, d+1)
    print('Lattice Dimension:', dim)
   

    

   
    ZERO = [0]*(2*n+1)
    for ecc in range(1,6):
        success = 0
        if(par>2):
           ecc = 5
        
        Prime = primes[ecc-1]
        print('NIST', Prime.nbits())
        b = bs[ecc-1]
        px = X_Coordinates[ecc-1]
        py = Y_Coordinates[ecc-1]
        BIT = bits[ecc-1]
            
        b = ZZ(b)
        E = EllipticCurve(GF(Prime),[0, 0, 0, a, b])
        P = E(px,py)
        Unknown = BIT - ceil(KNOWN[par]*BIT-1)
        print('Known bits', ceil(KNOWN[par]*BIT))
        
        
        for run in range(1,2+1):
            LLLT = []
            GBT = []
            h0 = floor(ZZ(P[0])/2^(Unknown))*2^Unknown
            e0 = ZZ(P[0])-h0



            ROOT = [e0]
            DD =[]
                
            BACK = Z[:n+1]     

            F = []
            H = []
            R = E.random_point()
            R1 = []
            R2 = []
            B_SET = []
            

            for i in range(n):
                mi = ZZ.random_element(Prime)
                Q = mi*R
                xQ = ZZ(Q[0])
                yQ = ZZ(Q[1])


                
                R = P + Q
                S = P - Q
             
                
                hi = ceil(ZZ(R[0])/2^(Unknown))*2^Unknown
                ei = ZZ(R[0])-hi

                hi1 = ceil(ZZ(S[0])/2^(Unknown))*2^Unknown
                ei1 = ZZ(S[0])-hi1


                hb = hi+hi1
                eb = ei+ei1 

                #ROOT.append(eb) 
              
                f = (h0 + e0 - xQ)^2*(hb + eb - 2*xQ) -2*(a + 3*xQ^2)*(h0 + e0 - xQ) - 4*yQ^2
                Ai = h0 - xQ
                Di = hb - 2*xQ                
                Ci = -2*(a + 3*xQ^2)*(Ai) - 4*yQ^2
                Ci = ZZ(Ci)
                Bi = -2*(a + 3*xQ^2)                
                f_i = (Ai +Z[0])^2*(Z[i+n+1])+Bi*Z[0]+Ci
                R2.append(eb+Di)
                BACK.append(Z[i+1]+Di)
                R1.append(eb)
                DD.append(Di)
                #Z1.append(Z[i-1]-Di)
                B_SET.append(Bi)


                #f_i = REDUCE(f_i, Prime)
                H.append(f_i)

                #print(f_i)

                f_i = (Ai +Z[0])^2*(Di+Z[i+1])+Bi*Z[0]+Ci
                f_i = REDUCE(f_i, Prime)
           
                F.append(f_i)


            #print(BACK)
            ROOT = [e0] + R1 + R2 

      
            while(1):
              SOL = Lattice(F,H,use_sage_lll=(par < 3))
              if(SOL!=0):
                 break 

           
            
            if(SOL[0] == ROOT[0] or SOL[1] == ROOT[0]):
                   success = success + 1
            LLLT.append(SOL[2])
            GBT.append(SOL[3])
            #print(success, '\t Avg. LLL time=', '%0.2f'%mean(LLLT),  '\tAvg. GB time=','%0.2f'% mean(GBT))
            #if(run==1):
                #print("Lattice Dimension:", SOL[4])
           
            print("Success:", success, '\t Avg. LLL time=',
                        f'{np.mean(LLLT):0.2f}', '\tAvg. GB time=', f'{np.mean(GBT):0.2f}')

    print('*******************************************************')




