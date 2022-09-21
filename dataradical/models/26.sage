R.<x,y> = F[]
modpol = y^6 + (3*x^2 + 4*x - 2)*y^5 + (3*x^4 + 10*x^3 - 9*x + 1)*y^4 + (x^6 + 7*x^5 + 8*x^4 - 14*x^3 - 11*x^2 + 6*x)*y^3 + (x^7 + 4*x^6 - x^5 - 13*x^4 + 2*x^3 + 10*x^2 - x)*y^2 - (x^6 - 7*x^4 - 4*x^3 + 2*x^2)*y - x^4 - x^3
rpol = (x^3*y + 3*x^2*y - x^2 + x*y^2) /((x+1)*(x^2*y+x^2+3*x*y+y^2))
spol = (x*y - x)/(x*y + y)

def polA(r,s):
	return (r*s^2 - 3*r*s + r + s^2)/((1 - s)*(r*s - 2*r + 1))
def polB(r,s):
	return (r*s^2 - 3*r*s + r + s^2)/((1 - s)^2*(r - s))
