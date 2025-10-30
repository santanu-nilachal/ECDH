from sage.all import (
    ZZ, QQ, GF, EllipticCurve, IntegerModRing, zero_matrix, Matrix,
    PolynomialRing, Set, binomial, prod, cputime
)

# ----------------------------
# Curve and base point (P-521)
# ----------------------------
Prime = ZZ("6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151")
a = -3
b = ZZ(int(
    "051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef10"
    "9e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00", 16
))
E = EllipticCurve(GF(Prime), [0, 0, 0, a, b])

px = int(
    "c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3d"
    "baa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66", 16
)
py = int(
    "11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e6"
    "62c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650", 16
)
P = E(px, py)

# ----------------------------
# Parameters
# ----------------------------
LSB = 83          # number of unknown LSBs

print("Number of unknown LSBs", LSB)

n   = 15          # samples
d   = 1           # degree cap in index set

# ----------------------------
# Polynomial ring and vars
# ----------------------------
R1 = PolynomialRing(QQ, ['x0'] + [f'y{i}' for i in range(1, n + 1)])
R1.inject_variables()     # gives x0, y1..yn
A  = list(R1.gens())[1:]  # [y1,...,yn]

# ----------------------------
# Build F polynomials
# ----------------------------
EB  = []   # eb = e_R + e_S for each sample
F   = []   # F_i polynomials
e0  = ZZ(P[0]) % (2 ^ LSB)
h0  = ZZ(P[0]) - e0

for i in range(n):
    Q = E.random_point()
    R = P + Q
    S = P - Q

    e  = ZZ(R[0]) % (2 ^ LSB); h  = ZZ(R[0]) - e
    e1 = ZZ(S[0]) % (2 ^ LSB); h1 = ZZ(S[0]) - e1

    hb = h + h1
    eb = e + e1
    EB.append(eb)

    # cons and f as in your original formula
    qx = ZZ(Q[0])
    cons = hb * (h0 - qx) ^ 2 - 2 * h0 ^ 2 * qx - 2 * (a + (qx) ^ 2) * h0 - 2 * a * qx - 4 * b

    f = (
        x0 ^ 2 * A[i] +
        (hb - 2 * qx) * x0 ^ 2 +
        2 * (h0 - qx) * x0 * A[i] +
        2 * (hb * (h0 - qx) - 2 * h0 * qx - a - (qx ^ 2)) * x0 +
        (h0 - qx) ^ 2 * A[i] +
        cons
    )
    F.append(f)

ROOT = [e0] + EB
ZERO = [0] * (n + 1)

# ----------------------------
# Index set I and monomials S
# ----------------------------
I, S = [], []
for i in range(2 ^ n):
    bits = ZZ(i).bits()
    if len(bits) < n:
        bits += [0] * (n - len(bits))
    bits = bits[:n]

    if sum(bits) <= d:
        PROD = prod(A[j] ^ bits[j] for j in range(n))
        for i0 in range(2 * d + 1):
            I.append([i0] + bits)
            S.append(x0 ^ i0 * PROD)

ls = len(S)

# ----------------------------
# Construct G polynomials
# ----------------------------
G = []
for k in range(len(I)):
    bits = I[k][1:]
    s    = sum(bits)
    i0   = I[k][0]

    if s == 0:
        G.append(x0 ^ i0 * (Prime ^ d))
        continue

    if s == 1:
        if i0 <= 1:
            ss = x0 ^ i0 * (Prime ^ d)
            for j in range(1, n + 1):
                ss *= A[j - 1] ^ I[k][j]
            G.append(ss)
        else:  # i0 >= 2
            ss = x0 ^ (i0 - 2) * (Prime ^ (d - 1))
            for j in range(1, n + 1):
                ss *= F[j - 1] ^ I[k][j]
            G.append(ss)
        continue

    # s >= 2
    if i0 >= 2 * s:
        ss = x0 ^ (i0 - 2 * s) * (Prime ^ (d - s))
        for j in range(1, n + 1):
            ss *= F[j - 1] ^ I[k][j]
        G.append(ss)
        continue

    # s >= 2 and i0 < 2*s  --> linear-combo construction
    J1 = [F[j - 1] for j in range(1, n + 1) if I[k][j] == 1]
    J2 = [A[j - 1] for j in range(1, n + 1) if I[k][j] == 1]

    R2  = IntegerModRing(Prime ^ (s - 1))
    MS  = zero_matrix(R2, 2 * s, 2 * s)
    a2  = prod(J2)
    G2  = [a2 * x0 ^ j for j in range(2 * s)]

    # Build G1: for v in {0,1}, and for each position r, replace J1[r] by J2[r]
    G1 = []
    for v in range(2):
        for r in range(len(J1)):
            f = x0 ^ v
            for c in range(len(J1)):
                f *= (J2[c] if c == r else J1[c])
            G1.append(f)

    for r in range(2 * s):
        for c in range(2 * s):
            MS[r, c] = (G1[r]).coefficient(G2[c])(ZERO)

    MSIN = MS.inverse()

    # Select the i0-th row combination
    f = sum(ZZ(MSIN[i0, j]) * G1[j] for j in range(2 * s))

    # Project onto S basis modulo p^(s-1)
    g = 0
    for j in range(ls):
        cij = ZZ((f.coefficient(S[j]))(ZERO)) % (Prime ^ (s - 1))
        g  += cij * S[j]

    G.append(g * (Prime ^ (d + 1 - s)))

print('Lattice Dimension', ls)

# ----------------------------
# Build integer matrix M
# ----------------------------
M = zero_matrix(ZZ, ls, ls)
X = ZZ.random_element(e0, 2 * e0)    # evaluation bound near root

PT  = [X] * (n + 1)
PT1 = [X] * (n + 1)
PT[0] *= x0
for i in range(1, n + 1):
    PT[i] *= A[i - 1]

for i in range(ls):
    f = G[i](PT)
    for j in range(ls):
        M[i, j] = ZZ(f.coefficient(S[j])(ZERO))


# ----------------------------
# LLL and reconstruction
# ----------------------------
tt = cputime()
M  = M.LLL()
print("LLL time:", cputime(tt))

POLY_SET = []
for i in range(ls):
    f = sum((M[i][j] / S[j](PT1)) * S[j] for j in range(ls))
    if f(ROOT) == 0:
        POLY_SET.append(f)
    else:
        break

# ----------------------------
# Gröbner basis (over QQ) and report
# ----------------------------
I_ideal = (POLY_SET) * R1
GB      = I_ideal.groebner_basis()
print("Groebner Basis", GB[0])
print("Root", e0)

