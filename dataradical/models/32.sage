R.<x,y> = F[]
modpol = x^4*(x - 1)^4*y^8 + 16*x^5*(x - 1)^3*y^7 + x*(x - 1)^2*(x^8 + 104*x^5 - 8*x^3 - 1)*y^6 + 4*x^2*(x - 1)*(3*x^8 + 88*x^5 - 24*x^3 - 3)*y^5 + 2*x*(27*x^10 - 3*x^8 + 332*x^7 - 216*x^5 + 12*x^3 - 27*x^2 + 3)*y^4 + 16*x^2*(x + 1)*(7*x^8 + 4*x^6 + 44*x^5 + 4*x^4 - 12*x^3 + 4*x^2 - 3)*y^3 + 2*x*(x + 1)^4*(53*x^6 - 106*x^5 + 205*x^4 - 96*x^3 + 35*x^2 + 10*x - 5)*y^2 + 8*x^2*(x + 1)^5*(5*x^4 - 10*x^3 + 18*x^2 - 10*x + 5)*y - (x - 1)^6*(x + 1)^6;

rpol = ((10*x^22 + 33*x^21 - 127*x^20 + 276*x^19 - 580*x^18 + 908*x^17 - 1500*x^16 + 1692*x^15 - 1352*x^14 + 1454*x^13 - 778*x^12 + 12*x^11 - 76*x^10 - 196*x^9 + 228*x^8 - 60*x^7 + 78*x^6 - 23*x^5 + x^4)/(x^26 + 18*x^25 + 145*x^24 + 712*x^23 + 2426*x^22 + 6140*x^21 + 11914*x^20 + 17592*x^19 + 17967*x^18 + 5990*x^17 - 23505*x^16 - 69296*x^15 - 121748*x^14 - 165592*x^13 - 186740*x^12 - 179216*x^11 - 147761*x^10 - 104642*x^9 - 63137*x^8 - 31896*x^7 - 13062*x^6 - 4068*x^5 - 822*x^4 - 40*x^3 + 33*x^2 + 10*x + 1))*y^7 + ((143*x^22 + 586*x^21 - 1285*x^20 + 2808*x^19 - 5780*x^18 + 8232*x^17 - 14644*x^16 + 11752*x^15 - 10718*x^14 + 12572*x^13 - 902*x^12 + 840*x^11 - 452*x^10 - 3160*x^9 + 444*x^8 - 808*x^7 + 423*x^6 - 54*x^5 + 3*x^4)/(x^26 + 18*x^25 + 145*x^24 + 712*x^23 + 2426*x^22 + 6140*x^21 + 11914*x^20 + 17592*x^19 + 17967*x^18 + 5990*x^17 - 23505*x^16 - 69296*x^15 - 121748*x^14 - 165592*x^13 - 186740*x^12 - 179216*x^11 - 147761*x^10 - 104642*x^9 - 63137*x^8 - 31896*x^7 - 13062*x^6 - 4068*x^5 - 822*x^4 - 40*x^3 + 33*x^2 + 10*x + 1))*y^6 + ((10*x^25 + 53*x^24 - 30*x^23 + 966*x^22 + 3664*x^21 - 3556*x^20 + 11333*x^19 - 21251*x^18 + 28139*x^17 - 55458*x^16 + 17976*x^15 - 47488*x^14 + 26764*x^13 + 14652*x^12 + 17494*x^11 + 13126*x^10 - 3852*x^9 + 565*x^8 - 2962*x^7 + 98*x^6 - 196*x^5 - 32*x^4 - 35*x^3 + 21*x^2 - x)/(x^26 + 18*x^25 + 145*x^24 + 712*x^23 + 2426*x^22 + 6140*x^21 + 11914*x^20 + 17592*x^19 + 17967*x^18 + 5990*x^17 - 23505*x^16 - 69296*x^15 - 121748*x^14 - 165592*x^13 - 186740*x^12 - 179216*x^11 - 147761*x^10 - 104642*x^9 - 63137*x^8 - 31896*x^7 - 13062*x^6 - 4068*x^5 - 822*x^4 - 40*x^3 + 33*x^2 + 10*x + 1))*y^5 + ((103*x^25 + 620*x^24 + 198*x^23 + 4048*x^22 + 11506*x^21 + 2092*x^20 + 25028*x^19 - 34564*x^18 + 41823*x^17 - 103288*x^16 - 39196*x^15 - 148480*x^14 - 58476*x^13 - 8472*x^12 + 28256*x^11 + 45304*x^10 + 21357*x^9 + 12236*x^8 + 2342*x^7 + 1040*x^6 + 74*x^5 + 44*x^4 - 244*x^3 + 44*x^2 - 3*x)/(x^26 + 18*x^25 + 145*x^24 + 712*x^23 + 2426*x^22 + 6140*x^21 + 11914*x^20 + 17592*x^19 + 17967*x^18 + 5990*x^17 - 23505*x^16 - 69296*x^15 - 121748*x^14 - 165592*x^13 - 186740*x^12 - 179216*x^11 - 147761*x^10 - 104642*x^9 - 63137*x^8 - 31896*x^7 - 13062*x^6 - 4068*x^5 - 822*x^4 - 40*x^3 + 33*x^2 + 10*x + 1))*y^4 + ((x^26 + 375*x^25 + 2466*x^24 + 2550*x^23 + 11190*x^22 + 22494*x^21 + 26326*x^20 + 39302*x^19 - 19201*x^18 + 11969*x^17 - 123052*x^16 - 177620*x^15 - 314604*x^14 - 326812*x^13 - 229204*x^12 - 118276*x^11 - 28193*x^10 + 10025*x^9 + 12842*x^8 + 10142*x^7 + 5238*x^6 + 1886*x^5 + 862*x^4 - 322*x^3 - 31*x^2 - x)/(x^26 + 18*x^25 + 145*x^24 + 712*x^23 + 2426*x^22 + 6140*x^21 + 11914*x^20 + 17592*x^19 + 17967*x^18 + 5990*x^17 - 23505*x^16 - 69296*x^15 - 121748*x^14 - 165592*x^13 - 186740*x^12 - 179216*x^11 - 147761*x^10 - 104642*x^9 - 63137*x^8 - 31896*x^7 - 13062*x^6 - 4068*x^5 - 822*x^4 - 40*x^3 + 33*x^2 + 10*x + 1))*y^3 + ((6*x^23 + 544*x^22 + 2194*x^21 - 2056*x^20 + 15222*x^19 - 14664*x^18 + 42938*x^17 - 54792*x^16 + 60644*x^15 - 84176*x^14 + 13684*x^13 - 95784*x^12 - 61020*x^11 - 52432*x^10 - 44508*x^9 - 8824*x^8 - 12522*x^7 + 528*x^6 - 742*x^5 + 432*x^4 + 486*x^3 - 72*x^2 + 2*x)/(x^23 + 15*x^22 + 97*x^21 + 375*x^20 + 995*x^19 + 1933*x^18 + 2755*x^17 + 2533*x^16 + 170*x^15 - 4874*x^14 - 11926*x^13 - 19066*x^12 - 23898*x^11 - 24774*x^10 - 21658*x^9 - 16022*x^8 - 9947*x^7 - 5077*x^6 - 2043*x^5 - 589*x^4 - 89*x^3 + 9*x^2 + 7*x + 1))*y^2 + ((6*x^22 + 242*x^21 + 850*x^20 - 1102*x^19 + 5768*x^18 - 7116*x^17 + 18072*x^16 - 24328*x^15 + 28612*x^14 - 37364*x^13 + 15324*x^12 - 38628*x^11 - 13640*x^10 - 19904*x^9 - 15112*x^8 - 3624*x^7 - 6202*x^6 + 402*x^5 - 958*x^4 + 354*x^3 + 48*x^2 - 4*x)/(x^22 + 14*x^21 + 83*x^20 + 292*x^19 + 703*x^18 + 1230*x^17 + 1525*x^16 + 1008*x^15 - 838*x^14 - 4036*x^13 - 7890*x^12 - 11176*x^11 - 12722*x^10 - 12052*x^9 - 9606*x^8 - 6416*x^7 - 3531*x^6 - 1546*x^5 - 497*x^4 - 92*x^3 + 3*x^2 + 6*x + 1))*y + (-4*x^21 + 18*x^20 + 175*x^19 - 177*x^18 + 1359*x^17 - 1023*x^16 + 3948*x^15 - 4532*x^14 + 4788*x^13 - 8976*x^12 + 642*x^11 - 10302*x^10 - 4686*x^9 - 6058*x^8 - 4228*x^7 - 1700*x^6 - 1704*x^5 - 90*x^4 - 281*x^3 + 71*x^2 - 9*x + 1)/(x^21 + 13*x^20 + 70*x^19 + 222*x^18 + 481*x^17 + 749*x^16 + 776*x^15 + 232*x^14 - 1070*x^13 - 2966*x^12 - 4924*x^11 - 6252*x^10 - 6470*x^9 - 5582*x^8 - 4024*x^7 - 2392*x^6 - 1139*x^5 - 407*x^4 - 90*x^3 - 2*x^2 + 5*x + 1)
spol = ((-x^11 + x^10 + x^9 - x^8 - 3*x^7 + 3*x^6 - x^5 + x^4)/(x^15 + 5*x^14 + 15*x^13 + 35*x^12 + 65*x^11 + 101*x^10 + 135*x^9 + 155*x^8 + 155*x^7 + 135*x^6 + 101*x^5 + 65*x^4 + 35*x^3 + 15*x^2 + 5*x + 1))*y^7 + ((-14*x^11 + 14*x^9 + 2*x^8 - 42*x^7 + 4*x^6 - 14*x^5 + 2*x^4)/(x^15 + 5*x^14 + 15*x^13 + 35*x^12 + 65*x^11 + 101*x^10 + 135*x^9 + 155*x^8 + 155*x^7 + 135*x^6 + 101*x^5 + 65*x^4 + 35*x^3 + 15*x^2 + 5*x + 1))*y^6 + ((-x^15 + x^13 - 75*x^12 - 3*x^11 + 84*x^10 + 23*x^9 - 242*x^8 + 49*x^7 - 60*x^6 + 23*x^5 + 5*x^4 + 3*x^3 + x)/(x^16 + 4*x^15 + 10*x^14 + 20*x^13 + 30*x^12 + 36*x^11 + 34*x^10 + 20*x^9 - 20*x^7 - 34*x^6 - 36*x^5 - 30*x^4 - 20*x^3 - 10*x^2 - 4*x - 1))*y^5 + ((-10*x^16 + 9*x^14 - 188*x^13 - 33*x^12 + 284*x^11 + 96*x^10 - 738*x^9 + 216*x^8 - 40*x^7 + 77*x^6 + 48*x^5 + 19*x^4 - 4*x^3 + 10*x^2 - 2*x)/(x^17 + 3*x^16 + 6*x^15 + 10*x^14 + 10*x^13 + 6*x^12 - 2*x^11 - 14*x^10 - 20*x^9 - 20*x^8 - 14*x^7 - 2*x^6 + 6*x^5 + 10*x^4 + 10*x^3 + 6*x^2 + 3*x + 1))*y^4 + ((-33*x^16 - 33*x^15 - x^14 - 213*x^13 - 351*x^12 + 217*x^11 + 401*x^10 - 871*x^9 - 467*x^8 - 131*x^7 - 115*x^6 + 9*x^5 + 35*x^4 - 5*x^3 + 19*x^2 + 3*x)/(x^17 + 3*x^16 + 6*x^15 + 10*x^14 + 10*x^13 + 6*x^12 - 2*x^11 - 14*x^10 - 20*x^9 - 20*x^8 - 14*x^7 - 2*x^6 + 6*x^5 + 10*x^4 + 10*x^3 + 6*x^2 + 3*x + 1))*y^3 + ((-x^15 - 38*x^14 - 5*x^13 - 14*x^12 - 91*x^11 - 246*x^10 + 425*x^9 - 276*x^8 - 295*x^7 - 18*x^6 - 155*x^5 - 30*x^4 - 13*x^3 - 18*x^2 + 7*x)/(x^15 + x^14 + 3*x^13 + 3*x^12 + x^11 + x^10 - 5*x^9 - 5*x^8 - 5*x^7 - 5*x^6 + x^5 + x^4 + 3*x^3 + 3*x^2 + x + 1))*y^2 + ((-4*x^14 - 8*x^13 - 25*x^12 + 36*x^11 - 71*x^10 - 48*x^9 + 110*x^8 - 56*x^7 - 138*x^6 + 56*x^5 - 101*x^4 + 20*x^3 - 27*x^2)/(x^14 + 3*x^12 + x^10 - 5*x^8 - 5*x^6 + x^4 + 3*x^2 + 1))*y + (-2*x^8 + 5*x^7 - x^6 - 9*x^5 + 13*x^4 - 9*x^3 + 5*x^2 - 3*x + 1)/(x^10 + 5*x^8 + 10*x^6 + 10*x^4 + 5*x^2 + 1)

def polA(q,t):
	return -q/t
def polB(q,t):
	return (-2*q*t - 2*q)/(q + t)