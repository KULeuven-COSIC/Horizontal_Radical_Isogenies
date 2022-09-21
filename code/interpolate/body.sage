F = Fp = GF(p)
load(path+'models/'+str(N)+'.sage')

r2 = modpol.degree(modpol.parent().gens()[len(modpol.parent().gens())-1])

dim = 1
m = r1

if os.path.exists(path+'kernels/'+str(N)+'/'+str(plist[0])+'/'+var+'/'+str(k)+'.sage'):
    S.<A,B> = GF(plist[0])[]
    num = A^(r1-1)
    den = A^(r1-1)
    load(path+'kernels/'+str(N)+'/'+str(plist[0])+'/'+var+'/'+str(k)+'.sage')
    if num in ZZ:
        r1 = 1
    else:
        r1 = num.degree(A)+1
    if den in ZZ:
        m = 1
    else:
        m = den.degree(A)+1

op = open(path+'samples/'+str(N)+'/'+str(p)+'/'+var+'/'+str(k)+'.txt','r')
data = list(op)

while True:
    
    knownum = 0
    knowden = 0
    
    A = 0
    B = 0

    if os.path.exists(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage'):
        load(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage')

    if knownum == 1:
        r1 = r2 = 1

    if knowden == 1:
        m = 1

    mat = []
    
    nentries = r1*r2+m+20

    for i in range(nentries):
        [A,B,v] = [Fp(d) for d in eval(data[i])]
        
        den = 1
        num = 1
        
        if os.path.exists(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage'):
            load(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage')
            
        mat += [[-v*den*A^j for j in range(m)]]
        monA = num
        for i in range(r1):
            mon = monA
            monA *= A
            for j in range(r2):
                (mat[-1]).append(mon)
                mon *= B

    ker = Matrix(mat).right_kernel()

    dim = ker.dimension()
    
    if dim == r1*r2+m:
        
        den = 1
        num = 0
        
        break

    if dim == 0:
        r1 += 20
        m = r1

    if dim > 1:
        m = m - dim + 1
        r1 = r1 - dim + 1

    if dim == 1:
        
        S.<A,B> = PolynomialRing(Fp)

        den = 1
        num = 1

        if os.path.exists(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage'):
            load(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage')

        vec = ker.basis()[0]
        denvec = vec[:m]
        numvec = vec[m:]

        mons = []
        monA = num
        for i in range(r1):
            mon = monA
            monA *= A
            for j in range(r2):
                mons.append(mon)
                mon *= B
        num = numvec.inner_product(vector(mons))
        mons = [den*A^j for j in range(m)]
        den = denvec.inner_product(vector(mons))
        
        break

if not os.path.exists(path+'kernels/'+str(N)+'/'):
    os.mkdir(path+'kernels/'+str(N)+'/')
if not os.path.exists(path+'kernels/'+str(N)+'/'+str(p)+'/'):
    os.mkdir(path+'kernels/'+str(N)+'/'+str(p)+'/')
if not os.path.exists(path+'kernels/'+str(N)+'/'+str(p)+'/'+var+'/'):
    os.mkdir(path+'kernels/'+str(N)+'/'+str(p)+'/'+var+'/')

op = open(path+'kernels/'+str(N)+'/'+str(p)+'/'+var+'/'+str(k)+'.sage','w')
op.write('num = '+str(num)+'\n\n')
op.write('den = '+str(den))
op.close()

progress = [['N='+str(N)]+[k for k in range(N)]]+[[variables[j]]+[0 for k in range(N)] for j in range(len(variables))]
for i in range(l):
    var = variables[i]
    for p in plist:
        for k in range(N):
            if os.path.exists(path+'kernels/'+str(N)+'/'+str(p)+'/'+var+'/'+str(k)+'.sage'):
                progress[i+1][k+1] += 1
print('\033['+str(l+2)+'A')
print(table(progress))
