N = # e.g. 17
r = # number of primes to use, e.g. 10
r1 = # rough estimate of the degree of the formulae in A, e.g. 100
threads = # number of threads to use

path = # '/home/<user>/dataradical/'
load(path+'primes/'+str(N)+'.sage')

def modmtoint(k,m):
    k = ZZ(k)
    if min(k,m-k) == k:
        return k
    return(k-m)

def crtlift(polylist,plist):
    m = prod(plist)
    ll = [list(poly) for poly in polylist]
    supp = list(set(flatten([[el[1] for el in l] for l in ll])))
    result = 0
    for mon in supp:
        coeffs = [(poly.coefficient(mon))(0,0) for poly in polylist]  
        term = mon * modmtoint(CRT(coeffs,plist),m)
        result += term
    return result

def maxcoeff(poly):
    if poly in ZZ:
        return abs(poly)
    else:
        return(max([abs(i[0]) for i in list(poly)]))

variables = ['xPA','yPA','newB','newA','snew','rnew','lmbda','cnew','bnew']
l = len(variables)
tuples = [[var,k] for var in variables for k in range(N)]
tuples.reverse()

for e in range(r):
    
    p = plist[e]

    load('makecode.sage')

    @parallel(ncpus=threads)
    def f(x):
        [var,k] = x
        load(str(N)+'/'+str(p)+'/'+var+'/'+str(k)+'.sage')

    list(f(tuples))

    # execute CRT lifts
    
    R.<A,B> = ZZ[]
    
    if not os.path.exists(path+'results/'+str(N)):
        os.mkdir(path+'results/'+str(N))
    
    @parallel(ncpus=threads)
    def g(x):
        [var,k] = x
        if not os.path.exists(path+'results/'+str(N)+'/'+var):
            os.mkdir(path+'results/'+str(N)+'/'+var)   
        denlist = []
        numlist = []
        pilist = []
        for i in range(e+1):
            pi = plist[i]
            load(path+'kernels/'+str(N)+'/'+str(pi)+'/'+var+'/'+str(k)+'.sage')
            denlist += [den]
            numlist += [num]
            pilist += [pi]
        if den in ZZ:
            denlift = modmtoint(den,pi)
        else:
            denlift = crtlift(denlist,pilist)
        if num in ZZ:
            numlift = modmtoint(num,pi)
        else:
            numlift = crtlift(numlist,pilist)
        if maxcoeff(denlift) < 10^-4 * prod(pilist):
            op = open(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage','w')
            op.write('knowden = 1'+'\n\n'+'den = '+str(denlift)+'\n\n')
            op.close()
        if maxcoeff(numlift) < 10^-4 * prod(pilist):
            op = open(path+'results/'+str(N)+'/'+var+'/'+str(k)+'.sage','a')
            op.write('knownum = 1'+'\n\n'+'num = '+str(numlift)+'\n\n')
            op.close()
    
    list(g(tuples))
