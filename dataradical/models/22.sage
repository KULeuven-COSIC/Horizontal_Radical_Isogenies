R.<x,y> = F[]
modpol = y^4 + (x^3 + 2*x^2 + x + 2)*y^3 + (x^5 + x^4 + 2*x^3 + 2*x^2 + 1)*y^2 + (x^5 - x^4 - 2*x^3 - x^2 - x)*y - x^4 - x^3
rpol = (x^2*y + x^2 + x*y + y)/(x^3 + 2*x^2 + y)
spol = (x*y + y)/(x^2 + y)

def polA(r,s):
	return (r*s - 2*r + 1)/(r - s)
def polB(r,s):
	return -s*(r*s - 2*r + 1)^2/((r - s)*(r - s^2 + s - 1))
