R.<x,y> = F[]
modpol = y^5 - (x^2 + 2)*y^4 - (2*x^3 + 2*x^2 + 2*x - 1)*y^3 + (x^5 + 3*x^4 + 7*x^3 + 6*x^2 + 2*x)*y^2 - (x^5 + 2*x^4 + 4*x^3 + 3*x^2)*y + x^3 + x^2
rpol = 1+x*(x+y)*(y-1)/((x+1)*(x^2-x*y+2*x-y^2+y))
spol = 1+x*(y-1)/((x+1)*(x-y+1))

def polA(r,s):
	return (1 - s)*(r*s - 2*r + 1)/(r*s^2 - 3*r*s + r + s^2)
def polB(r,s):
	return (s - 1)*(r^2*s - 3*r^2 + r*s + 3*r - s^2 - 1)/((r - s)*(r*s^2 - 3*r*s + r + s^2))
