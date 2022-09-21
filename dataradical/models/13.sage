R.<x,y> = F[]
modpol = y^2 + (x^3 + x^2 + 1)*y - x^2 - x
rpol = -x*y + 1
spol = 1-x*y/(y + 1)

def polA(r,s):
	return (1 - r)*(s - 1)/(r - s)
def polB(r,s):
	return (r - s)/(s - 1)
