R.<x,y> = F[]
modpol = y^4 + (x^3 + x^2 - x + 2)*y^3 + (x^3 - 3*x + 1)*y^2 - (x^4 + 2*x)*y + x^3 + x^2
rpol = (x^2 + x - y)/(x^2 + x*y + x - y^2 - y)
spol = (x + 1)/(x + y + 1)

def polA(r,s):
    return (s - 1)*(r - s)/(r*s^2 - 3*r*s + r + s^2)
def polB(r,s):
    return (1 - s)*(r*s - 2*r + 1)/(r*s^2 - 3*r*s + r + s^2)