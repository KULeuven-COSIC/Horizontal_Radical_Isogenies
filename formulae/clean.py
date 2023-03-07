for N in [17,19,21,23,25,27,29,31,37,41]:

	for var in ['newA', 'newB']:

		path = str(N) + '/' + var + '/'

		for i in range(N):

			with open(path + str(i) + '.sage','r') as op:
				content = op.readlines()
				op.close()
				
			if len(content) > 4:

				with open(path + str(i) + '.sage','w') as op:
					op.write(content[2] + '\n')
					op.write(content[6])
					op.close()
