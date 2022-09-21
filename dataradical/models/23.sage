R.<x,y> = F[]
modpol = y^7 + (x^5 - x^4 + x^3 + 4*x^2 + 3)*y^6 + (x^7 + 3*x^5 + x^4 + 5*x^3 + 7*x^2 - 4*x + 3)*y^5 + (2*x^7 + 3*x^5 - x^4 - 2*x^3 - x^2 - 8*x + 1)*y^4 + (x^7 - 4*x^6 - 5*x^5 - 6*x^4 - 6*x^3 - 2*x^2 - 3*x)*y^3 - (3*x^6 - 5*x^4 - 3*x^3 - 3*x^2 - 2*x)*y^2 + (3*x^5 + 4*x^4 + x)*y - x^2*(x+1)^2
rpol = (x^2 + x + y + 1)/(x^2 - x*y)
spol = (x + y + 1)/x

def polA(r,s):
	return (r - s)/(r*s - 2*r + 1)
def polB(r,s):
	return (r - s^2 + s - 1)/(r*s - 2*r + 1)
