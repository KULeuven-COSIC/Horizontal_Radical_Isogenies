if not os.path.exists(str(N)):
    os.mkdir(str(N))

if not os.path.exists(str(N)+'/'+str(p)):
    os.mkdir(str(N)+'/'+str(p))

for var in variables:
    
    if not os.path.exists(str(N)+'/'+str(p)+'/'+var):
        os.mkdir(str(N)+'/'+str(p)+'/'+var)
    
    for k in range(N):
        
        op = open('body.sage','r')
        content = op.read()
        op.close()

        op = open(str(N)+'/'+str(p)+'/'+var+'/'+str(k)+'.sage','w')
        op.write('var = '+'\''+var+'\''+'\n\n'+'k = '+str(k)+'\n\n'+content)
        op.close()
