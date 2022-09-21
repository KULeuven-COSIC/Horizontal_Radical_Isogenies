R.<x,y> = F[]
modpol = y^2 + (x^3 - 2*x^2 + 3*x + 1)*y + 2*x
rpol = (x^2 - x*y - 3*x + 1)/((x-1)^2*(x*y+1))
spol = (x^2 - 2*x - y)/(x^2 - x*y - 3*x - y^2 - 2*y)

def polA(r,s):
	return s*(r^2*s - 3*r^2 + r*s + 3*r - s^2 - 1)/((r - s)*(r*s^2 - 3*r*s + r + s^2))
def polB(r,s):
	return (-2*r^2*s^2 + 5*r^2*s - r^2 + r*s^3 - 2*r*s^2 - 4*r*s + r + 2*s^2)/(s*(r - s)*(r*s - 2*r + 1))
