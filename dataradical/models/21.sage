R.<x,y> = F[]
modpol = y^4 + (3*x^2 + 1)*y^3 + (x^5 + x^4 + 2*x^2 + 2*x)*y^2 + (2*x^4 + x^3 + x)*y + x^3
rpol = 1+(y^2+y)*(x*y+y+1)/((x*y+1)*(x*y-y^2+1))
spol = 1+(y^2+y)/(x*y+1)

def polA(r,s):
	return (1 - s)*(r^2*s - 3*r^2 + r*s + 3*r - s^2 - 1)/((r - s^2 + s - 1)*(r*s - 2*r + 1))
def polB(r,s):
	return (r - s^2 + s - 1)/(r*s - 2*r + 1)
