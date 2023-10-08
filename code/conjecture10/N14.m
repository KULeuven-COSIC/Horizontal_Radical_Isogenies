// Verifies Conjecture 10 for N = 14

// Construction E,P in Tate Normal Form using Sutherland's model for X_1(14)

F<A> := FunctionField(Rationals());
P1<y>:=PolynomialRing(F);
K<B> := ext<F|y^2+(A^2+A)*y+A>;
r := 1-(A+B)/((B+1)*(A+B+1));
s := (1-A)/(B+1);
b := r*s*(r-1);
c := s*(r-1);
E := EllipticCurve([K|1-c,-b,-b,0,0]);
P := E![0,0];

// Computing the codomain curve E/<P>

rho := TatePairing(P,-P,14);
P2<z> := PolynomialRing(K);
L<a> := ext<K|z^2-rho>;
P3<t> := PolynomialRing(L);
ker := &*{(z-(n*P)[1]) : n in [1..Order(P)-1]};
E2,phi := IsogenyFromKernel(E,ker);

a1 := aInvariants(E2)[1];
a3 := aInvariants(E2)[2];
a2 := aInvariants(E2)[3];
a4 := aInvariants(E2)[4];
a6 := aInvariants(E2)[5];

Psi := DivisionPolynomial(E2,2);
rts := Roots(Psi);
Psiq := Psi/(z-rts[1,1]);
PsiqL := P3!Evaluate(Psiq,t);
rtsq := Roots(PsiqL);

// Computing (the two options for) rho_14' up to squares

E3 := BaseChange(E2,L);
x1 := rtsq[1,1];
y1 := -1/2*(a1*x1+a3);
P1 := E3![x1,y1];
x2 := rtsq[2,1];
y2 := -1/2*(a1*x2+a3);
P2 := E3![x2,y2];

T1 := TatePairing(P1,P1,2);
T2 := TatePairing(P2,P2,2);

// Verifying the conjecture

function IsSquareFunction(g)
  supp, mult := Support(Divisor(g));
  halfdiv := &+[(mult[i] div 2)*supp[i] : i in [1..#mult]];
  return IsPrincipal(halfdiv);
end function;

bE := bInvariants(E);
sqrtPpoly := t^4-bE[2]*t^2-2*bE[3]*t-bE[4];
disc1 := Discriminant(Factorization(sqrtPpoly)[1,1]);
disc2 := Discriminant(Factorization(sqrtPpoly)[2,1]);

IsSquareFunction(T1*a/disc2/b);
