R.<u,v> = F[]
modpol = (u-1)^2*v^6+(u-1)^2*(u^3+2)*v^5-(u-1)^2*(u^5+2*u^4-2*u^3-u^2-2*u-1)*v^4+u*(u-1)*(u^6-3*u^5-4*u^4+u^3+u^2+3*u-2)*v^3+u*(u-1)*(u^2+u+1)*(3*u^4-4*u^3-2*u^2+u-1)*v^2+3*u^5*(u-1)*(u^2+u+1)*v+u^6*(u^2+u+1)
G = -1/u
x = v/(u*v+u)
y = (G^4*x + G^4 + G^3*x - 2*G^2*x^2 - G*x^3 + G + x)/(G^4 + G^3*x - G^2*x^2 - G*x^2 + G + x)
rpol = (x^2*y - x*y + y - 1) / (x^2*y - x)
spol = (x*y - y + 1) / (x*y)

def polA(r,s):
    x = (-r + s)/(r*s - 2*r + 1)
    y = (-r*s + 2*r - 1)/(r - s^2 + s - 1)
    return (x^2*y^2 - 2*x^2*y - x*y^3 + 2*x*y^2 - y + 1)/((y - x)*(x^2*y - x*y^2 + y - 1))
def polB(r,s):
    x = (-r + s)/(r*s - 2*r + 1)
    y = (-r*s + 2*r - 1)/(r - s^2 + s - 1)
    return x*(x^2*y^2 - 2*x^2*y - x*y^3 + 2*x*y^2 - y + 1)/(y*(1 - x)*(x^2*y - x^2 - x*y^2 + x*y - x + y - 1))
