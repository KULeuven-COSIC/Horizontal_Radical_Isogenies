path = # '/home/<user>/dataradical/'

N = # e.g. 17
r = # number of primes to use, e.g. 10

load('makecode.sage')

@parallel(ncpus=r)
def f(x):
    load(str(N)+'/'+str(x)+'.sage')

list(f(list(range(r))))
