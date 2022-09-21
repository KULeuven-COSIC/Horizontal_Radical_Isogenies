samplesize = 0

load(path+'primes/'+str(N)+'.sage')

p = plist[e]

F = Fp = GF(p)

load(path+'models/'+str(N)+'.sage')

rpoldenom = rpol.denominator()
if rpoldenom == 1:
	rpoldenom = x-x+1
spoldenom = spol.denominator()

D = (2^2-4*p)/N^4
o = ZZ[(-D + sqrt(D))/2]

print('N =',N)
print('p =',p)
print('D =',D)
print('class number =',o.class_number())

def denomfp(x):
    var = modpol.parent().gens()[len(modpol.parent().gens())-1]
    deg = modpol.degree(var)
    F = Fp
    QA.<A> = FunctionField(F)
    QAB.<B> = QA[]
    thing = QAB(eval(str(x).replace('^','**')))
    denom = lcm([thing[j].denominator() for j in range(deg+1)])
    return denom

S.<A,B> = Fp[]
QA.<A> = FunctionField(Fp)
QAB.<B> = QA[]
QB.<B> = QA.extension(QAB(S(modpol)))
r = rpol(A,B)
s = spol(A,B)
b = r*s*(r-1)
c = s*(r-1)
E = EllipticCurve([1-c,-b,-b,0,0])
P = E(0,0)
Ej = E.j_invariant()
denomEj = denomfp(Ej)
numEj = denomEj * Ej

RR.<A> = Fp[]
rts = []
for d in divisors(D):
    if d.is_square() and ((D/d)%4==0 or (D/d)%4==1):
        Dd = D/d
        rts += RR(hilbert_class_polynomial(Dd)).roots()
Alist = []
for rt in rts:
    j = rt[0]
    poly = RR(QA((numEj - j*denomEj).norm()).numerator())
    Alist += [r[0] for r in poly.roots()]

def findBs(a):
    S.<A,B> = Fp[]
    R.<y> = Fp[]
    rts = R(S(modpol)(a,y)).roots()
    if not rts == []:
        return([[a,rt[0]] for rt in rts])

ABlist = []
for A in set(Alist):
    ABlist += findBs(A)
    
MAX = len(ABlist)
    
print('length ABlist =',MAX)

if samplesize == 0:
    samplesize = MAX

print('going for',samplesize,'samples')

def disc(b,c):
    return b^3*(c^4 - 8*b*c^2 - 3*c^3 + 16*b^2 - 20*b*c + 3*c^2 + b - c)

RR.<A> = Fp[]

if not os.path.exists(path+'samples/'+str(N)+'/'):
    os.mkdir(path+'samples/'+str(N)+'/')

if os.path.exists(path+'samples/'+str(N)+'/'+str(p)):
    import shutil
    shutil.rmtree(path+'samples/'+str(N)+'/'+str(p))

os.mkdir(path+'samples/'+str(N)+'/'+str(p))

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/xPA')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/yPA')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/bnew')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/cnew')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/rnew')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/snew')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/newA')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/newB')

os.mkdir(path+'samples/'+str(N)+'/'+str(p)+'/lmbda')

ctr = -1
done = False
for t in range(samplesize):
    
    print('finding E...')
    
    while True:
        ctr += 1
        if ctr == MAX:
            done = True
            break
        [A,B] = ABlist[ctr]
        if not rpoldenom(A,B) == 0 and not spoldenom(A,B) == 0:
            r = rpol(A,B)
            s = spol(A,B)
            b = r*s*(r-1)
            c = s*(r-1)            
            if not disc(b,c) == 0:
                E = EllipticCurve([1-c,-b,-b,0,0])
                
                print('checking E...')
                
                if gcd(E.order(),N^5) == N^4 and gcd(E.abelian_group().exponent(),N^3) == N^2:
                    break
    
    if done == True:
        break
    
    print('finding Q...')

    P = E(0,0)
    cofactor = ZZ(order(E)/N^4)
    
    while True:
        Q = cofactor*(E.random_element())
        if N*Q == P:
            break
    
    print('finding R...')

    while True:
        R = cofactor*E.random_element()
        if N*R == E(0) and P.weil_pairing(R,N).multiplicative_order() == N:
            break
    
    print('finding gammalist...')
    
    zeta = P.weil_pairing(R,N)^(-1)
    
    Svec = vector([sum([(Q + j*R + i*P)[0] for i in range(N)]) for j in range(N)])

    vdM = Matrix(Fp,[[zeta^(d*j) for j in range(N)] for d in range(N)])

    gammavec = vdM * Svec

    gammalist = list(gammavec)  
        
    print('finding deltalist...')
    
    Syvec = vector([sum([(Q + j*R + i*P)[1] for i in range(N)]) for j in range(N)])

    deltavec = vdM * Syvec

    deltalist = list(deltavec)
    
    print('finding alp...')
    
    gamma1 = gammalist[1]
    
    alp = gamma1/(N^2*b)
    
    print('computing EA...')
    
    phi = E.isogeny(P)
    EA = phi.codomain()
    [a1,a2,a3,a4,a6] = EA.a_invariants()
    
    print('formal expressions...')
    
    S.<X> = Fp[]
    F.<w> = S.quotient(X^N - alp^N)
    
    fx = sum([gammalist[i]/(N*alp^i) * w^i for i in range(N)]) - sum((i*P)[0] for i in range(1,N))
    fy = sum([deltalist[i]/(N*alp^i) * w^i for i in range(N)]) - sum((i*P)[1] for i in range(1,N))
    
    deni = (2*fy+a1*fx+a3)^(-1)
    
    slope = (3*fx^2+2*a2*fx+a4-a1*fy)*deni
    
    nu = (-fx^3+a4*fx+2*a6-a3*fy)*deni
    
    fxmin2p = slope^2+a1*slope-a2-2*fx
    fymin2p = slope*fxmin2p+nu
    
    z = (fymin2p-fy)/(fxmin2p-fx)
    
    d = 3*fx-z^2-a1*z+a2
    
    lmbda = (a1*fx+2*fy+a3)/d
    
    lambdainv = lmbda^(-1)
    
    fb = -d*lambdainv^2
    
    fc = 1-(a1+2*z)*lambdainv
    
    fr = fb/fc
    
    fs = fc/(fr-1)
    
    fA = polA(fr,fs)
    
    fB = polB(fr,fs)
    
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'xPA/'+str(i)+'.txt','a')
        op.write(str([A,B,fx[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'yPA/'+str(i)+'.txt','a')
        op.write(str([A,B,fy[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'bnew/'+str(i)+'.txt','a')
        op.write(str([A,B,fb[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'cnew/'+str(i)+'.txt','a')
        op.write(str([A,B,fc[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'rnew/'+str(i)+'.txt','a')
        op.write(str([A,B,fr[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'snew/'+str(i)+'.txt','a')
        op.write(str([A,B,fs[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'newA/'+str(i)+'.txt','a')
        op.write(str([A,B,fA[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'newB/'+str(i)+'.txt','a')
        op.write(str([A,B,fB[i]])+'\n')
        
    for i in range(N):
        op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+'lmbda/'+str(i)+'.txt','a')
        op.write(str([A,B,lmbda[i]])+'\n')
        
    print('found',t+1,'samples so far')
    print('processed',str(ctr)+'/'+str(samplesize))
