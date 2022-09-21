R.<u,v> = F[]
modpol = u*v^5 + (u^4 - 2*u^3 - u^2 + 2*u + 1)*v^4 - (2*u^6 - 2*u^4 + 4*u^3 + 2*u^2 - 2)*v^3 + (u^8 + u^7 - 2*u^6 + u^5 - u^4 - u^3 - 2*u^2 - u + 1)*v^2 + (u^8 + u^7 + 2*u^6 + u^5 - 2*u^4 + u^3 - u^2)*v + u^6
y = (u-v-1)/u
x = -(v+1)*(u^4 + u^3*v + u^3 - u*v^2 - v)/(u^2*(u^3 + u^2*v + u^2 - u*v - u - v^2 - v))
rpol = (x^2*y - x*y + y - 1) / (x^2*y - x)
spol = (x*y - y + 1) / (x*y)

def polA(r,s):
    x = (-r + s)/(r*s - 2*r + 1)
    y = (-r*s + 2*r - 1)/(r - s^2 + s - 1)
    return x*(1 - y)*(x^2*y - x*y^2 - x*y + y^2 - 1)/((x - y + 1)*(x^2*y - x*y^2 + y - 1))
def polB(r,s):
    x = (-r + s)/(r*s - 2*r + 1)
    y = (-r*s + 2*r - 1)/(r - s^2 + s - 1)
    return -(x - y + 1)*(x^4*y - x^3*y^2 - 3*x^3*y + 3*x^2*y^2 + 2*x^2*y - x^2 - 2*x*y^2 + x + y - 1)/(x*(x - y)*(x^2*y^2 - 2*x^2*y - x*y^3 + 2*x*y^2 - x*y + y^2 - 2*y + 1))
