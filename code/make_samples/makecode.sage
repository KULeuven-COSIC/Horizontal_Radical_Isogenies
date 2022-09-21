if not os.path.exists(str(N)):
    os.mkdir(str(N))

op = open('blank.sage','r')
content = op.read()
op.close()

for i in range(r):
    op = open(str(N)+'/'+str(i)+'.sage','w')
    op.write('N = '+str(N)+'\n\n'+'e = '+str(i)+'\n\n'+content)
    op.close()
