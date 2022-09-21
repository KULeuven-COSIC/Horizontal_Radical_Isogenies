/*

This file contains the formulas for radical N-isogenies for N = 2,...,19
More precisely, let E be an elliptic curve such that P = (0,0) is an N-torsion point. We give
formulas for an isomorpic form Eiso of EA = E/<P> such that Eiso has the same form as E, with
P'=(0,0) on Eiso such that Eiso -> Eiso/<P'> is a cyclic extension of the isogeny with kernel
<P>. Furthermore, P' on Eiso is P-distinguished, i.e. the image of P' under the dual isogeny
is P = (0,0) on E. The expressions involving Eiso are denoted such that they are easy to read
in the form of a Horner scheme when viewed as a polynomial in the radical.

For N = 2 we use the Montgomery form of an elliptic curve.
For N = 3 we use a Weierstrass form that is isomorphic to a Hessian form.
For N > 3 we use the Tate normal form of an elliptic curve.
From N = 6 onwards, we use the optimized equations for Tate normal forms by Sutherland that can
be found here: http://math.mit.edu/~drew/X1_optcurves.html

Remark that instead of using the assertion IsIsomorphic(Eiso,EA) we compare their j-invariants
by means of a self-written function since IsIsomorphic constructs a hard-to-compute isomorphism
as well. The reason for the self-written function is that it avoids constructing an elliptic
curve over this field, while also avoiding inversions in the computations of the j-invariants.

Putting the global variable SYMBOLIC_PROOFS to false will set one of the two parameters as the
(fixed) value 1013. Putting this parameter to true can result in the code having to run for an
extremely long time for larger N.

*/


clear;

SYMBOLIC_PROOFS := false;

if SYMBOLIC_PROOFS then
 QA<A> := FunctionField(Rationals());
else
 QA := Rationals(); A := 101;
end if;


function same_j_invars(EA, newb, newc)
  a_1 := 1-newc; a_2 := -newb; a_3 := -newb; a_4 := 0; a_6 := 0;
  b_2 := a_1^2 + 4*a_2;
  b_4 := a_1*a_3 + 2*a_4;
  b_6 := a_3^2 + 4*a_6;
  b_8 := a_1^2*a_6 + 4*a_2*a_6 - a_1*a_3*a_4 + a_2*a_3^2 - a_4^2;
  c_4 := b_2^2 - 24*b_4;
  c_6 := -b_2^3 + 36*b_2*b_4 - 216*b_6;
  d := -b_2^2*b_8 - 8*b_4^3 - 27*b_6^2 + 9*b_2*b_4*b_6;
  return jInvariant(EA)*d eq c_4^3;
end function;



N := 2;
QAB<B> := FunctionField(QA);
E := EllipticCurve([0,A,0,B,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QAB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QAB | z^N - t>;
assert w^N eq 4*B;
newA := -3*w + A;
newB := -2*A*w + 8*B;
Eiso := EllipticCurve([0,newA,0,newB,0]);
assert jInvariant(EA) eq jInvariant(Eiso);
"Formulas verified for N equal", N;



N := 3;
QAB<B> := FunctionField(QA);
E := EllipticCurve([A,0,B,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QAB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QAB | z^N - t>;
assert w^N eq -B;
newA := -6*w + A;
newB := 3*A*w^2 - A^2*w + 9*B;
Eiso := EllipticCurve([newA,0,newB,0,0]);
assert jInvariant(EA) eq jInvariant(Eiso);
"Formulas verified for N equal", N;



N := 4;
b := -A; c := 0;
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq A;
numA := w*(4*w^2+1);
denA := (2*w+1)^4;
newA := numA/denA;
newb := -newA; newc := 0;
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 5;
b := A; c := A;
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq A;
numA := w * (w^4 + 3*w^3 + 4*w^2 + 2*w + 1);
denA := (w^4 - 2*w^3 + 4*w^2 - 3*w + 1);
newA := numA/denA;
newb := newA; newc := newA;
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 6;
r := A; s := 1;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq -A^2*(A-1);
numA := (-3*A + 2)*w^4 + 3*A^2*w^2 + 2*A*w - 3*A^3 + 4*A^2;
denA := w^4 + 2*A*w^2 + 3*A*w + A^2;
newA := numA/denA;
newr := newA; news := 1;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 7;
r := A; s := A;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq A^4*(A-1);
numA := w^6 + A*w^5 + 2*A^3*w^2 - A^3*w + A^4;
denA := -w^6 + A*w^4 + A^3*w^2 - 2*A^3*w + A^4;
newA := numA/denA;
newr := newA; news := newA;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 8;
r := 1/(2-A); s := A;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq -A*b^3/c^2;
numA := -2*A*(A - 2)*w^2 - A*(A - 2);
denA := (A - 2)^2*w^4 - A*(A-2)*w^2 - A*(A-2)*w + A;
newA := numA/denA;
newr := 1/(2-newA); news := newA;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 9;
r := A^2-A+1; s := A;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
assert w^N eq A^4*(A-1)*(A^2-A+1)^3;
numA := ((A*(A^2 - A + 1))*((w^3 + A*(A^2 - A + 1))*w^2 + (A*(A^2 - A + 1))^2));
denA := (((w^3 - A*(A^2 - A + 1)*(A-1))*w^3 - A^3*(A^2 - A + 1)^2)*w + (A*(A^2 - A + 1))^3);
newA := numA/denA;
newr := newA^2-newA+1; news := newA;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 10;
r := -A^2/(A^2-3*A+1); s := A;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
/*
Alternative:
numA := (A^6 - 5*A^5 + 5*A^4 + 5*A^3 - 5*A^2 + A)*w^6 + (2*A^6 - 14*A^5 + 34*A^4 -
    34*A^3 + 14*A^2 - 2*A)*w^5 + (-2*A^6 + 7*A^5 - 3*A^4 - 6*A^3 + 5*A^2 -
    A)*w^4 + (-4*A^6 + 16*A^5 - 17*A^4 + 7*A^3 - A^2)*w^3 + (6*A^6 - 7*A^5 +
    2*A^4)*w^2 + (2*A^7 + 3*A^6 - 4*A^5 + A^4)*w;
denA := (A^6 - 2*A^5 - 15*A^4 + 50*A^3 - 45*A^2 + 16*A - 2)*w^6 + (3*A^6 - 18*A^5 +
    32*A^4 - 12*A^3 - 8*A^2 + 6*A - 1)*w^5 + (2*A^5 - 5*A^4 - 2*A^3 + 4*A^2 -
    A)*w^4 + (-4*A^6 + 18*A^5 - 24*A^4 + 12*A^3 - 2*A^2)*w^3 + (8*A^6 - 6*A^5 +
    A^4)*w^2 + (6*A^7 - 5*A^6 + A^5)*w + 2*A^7 - 3*A^6 + A^5;
newA := numA/denA;
*/
assert w^N eq A^9*(2*A-1)^2*(A-1)/(A^2-3*A+1)^5;
u := 1
   + w*(3
   + w*((4*A - 1)/A
   + w*(2*c/b
   + w*(-c*(A - 4)/(A*b)
   + w*((A-1)*(4*A - 1)/(A*b)
   + w*((A+1)*(A-1)/(A^2*b)
   + w*(4*c*(A-1)/(A*b^2)
   + w*(c*(A-1)*(4*A - 1)/(A^2*b^2)
   + w*(-c^2*(A-1)/(A*b^3)
)))))))));
vA := A
    + w*(2
    + w*((A+1)/A
    + w*(3*c/b
    + w*(c*(A+1)/(A*b)
    + w*((A-1)*(A+1)/(A*b)
    + w*((A-1)*(4*A - 1)/(A^2*b)
    + w*(c*(A-1)/(A*b^2)
    + w*(c*(A+1)*(A-1)/(A^2*b^2)
    + w*(c^2*(A-1)/(A*b^3)
)))))))));
newA := vA/u;
newr := -newA^2/(newA^2-3*newA+1); news := newA;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 11;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^2 + 1)*B + A;
QB<B> := ext<QA | modpol>;
r := A*B+1; s := -A+1;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QBz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq b^3*(A^2+A*B-A-B)*(A*B+1)/c^2;
u :=
    1
    + w*(A-3
    + w*(3
    + w*(-2*c/b
    + w*(A*(4*B+1)/b
    + w*(A*(A+3)/b
    + w*(A^2*(B-2*A+3)/(b*c)
    + w*(A^2*(B+A^2-2)/(b*c)
    + w*(4*A^2/b^2
    + w*(A^3*((3*A-2)*B+A)/(b^2*c)
    + w*(A^4/(b^2*c)
))))))))));
vA :=
    A
    + w*(B+2*A
    + w*(-B*c/b
    + w*((A-1)*B*(B-2*A+1)/b
    + w*(A*(2*B+1)/b
    + w*(2*A*(A+1)/b
    + w*(2*A^2*(B+A)/(b*c)
    + w*(A^2*(3*B+3*A^2+2)/(b*c)
    + w*(3*A^2/b^2
    + w*(A^3*((A+2)*B+2*A+1)/(b^2*c)
    + w*(A^3*(3*A-1)/(b^2*c)
))))))))));
vB :=
    B
    + w*(-B+A+1
    + w*(-2
    + w*(A*(-2*B^2-(2*A+1)*B-1)/b
    + w*(A*(-2*B+1)/b
    + w*(A^2*B*(-B+3*A-4)/(b*c)
    + w*(A^2*(A-1)/(b*c)
    + w*(-A^2*(B+A^2)/(b*c)
    + w*(A^2*(B-2)/b^2
    + w*(-2*A^3*(A*B+1)/(b^2*c)
    + w*(-A^3*(2*A-1)/(b^2*c)
))))))))));
uinv := 1/u;
newA := vA*uinv;
newB := vB*uinv;
newr := newA*newB+1; news := -newA+1;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 12;
r := (2*A^2-2*A+1)/A; s := (3*A^2-3*A+1)/A^2;
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QA);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QA | z^N - t>;
/*
Alternative:
numA := A^5*w^7 + (A^6 - A^5)*w^6 + (4*A^6 - 6*A^5 + 4*A^4 - A^3)*w^5 + (4*A^7 - 10*A^6 + 10*A^5 - 5*A^4 + A^3)*w^4 + (12*A^7 - 42*A^6 + 64*A^5 - 55*A^4 + 28*A^3 - 8*A^2 + A)*w^3 - 24*A^9 + 84*A^8
    - 140*A^7 + 140*A^6 - 90*A^5 + 37*A^4 - 9*A^3 + A^2;
denA := A^5*w^7 + (A^5 - A^4)*w^6 + (4*A^6 - 6*A^5 + 4*A^4 - A^3)*w^5 + (8*A^7 - 20*A^6 + 20*A^5 - 10*A^4 + 2*A^3)*w^4 + (24*A^7 - 84*A^6 + 128*A^5 - 110*A^4 + 56*A^3 - 16*A^2 + 2*A)*w^3 + (24*A^7
    - 84*A^6 + 140*A^5 - 140*A^4 + 90*A^3 - 37*A^2 + 9*A - 1)*w^2 + (-24*A^8 + 84*A^7 - 140*A^6 + 140*A^5 - 90*A^4 + 37*A^3 - 9*A^2 + A)*w - 48*A^9 + 192*A^8 - 364*A^7 + 420*A^6 - 320*A^5 +
    164*A^4 - 55*A^3 + 11*A^2 - A;
newA := numA/denA;
*/
assert w^N eq -(A-1)*(2*A-1)^2*(3*A^2-3*A+1)^3*(2*A^2-2*A+1)^4/A^11;
u := (3*A^2-3*A+1)/A^2
   + w*(3
   + w*(3
   + w*(c*(3*A - 1)/(A*b)
   + w*(3*(A-1)*(2*A-1)/(A*b)
   + w*(3*(A-1)*(2*A-1)/(A^2*b)
   + w*((A-1)*(3*A - 1)/(A*(2*A^2-2*A+1)*b)
   + w*(3*(A-1)/((2*A^2-2*A+1)*b)
   + w*(3*(A-1)^2*(2*A-1)/(A^2*b^2)
   + w*(3*(A-1)^2*(2*A-1)/(A*(2*A^2-2*A+1)*b^2)
   + w*(3*(A-1)^2*(2*A-1)/(A*(2*A^2-2*A+1)*b^2)
))))))))));	// Remark: coefficient at w^11 equals zero so one less coefficient
vA := (-2*A^3 + 6*A^2 - 4*A + 1)/A^2
   + w*(2
   + w*(2
   + w*(2*c/b
   + w*((A-1)*(2*A-1)*(4*A^2 - 2*A + 1)/(A^3*b)
   + w*(2*(A-1)*(2*A-1)/(A^2*b)
   + w*(2*A*(A-1)/((2*A^2-2*A+1)*b)
   + w*(2*(A-1)/((2*A^2-2*A+1)*b)
   + w*(2*(A-1)^2*(2*A-1)/(A^2*b^2)
   + w*(2*(A-1)^2*(2*A-1)/(A*(2*A^2-2*A+1)*b^2)
   + w*(2*(A-1)^2*(2*A-1)/(A*(2*A^2-2*A+1)*b^2)
))))))))));	// Remark: coefficient at w^11 equals zero so one less coefficient
newA := vA/u;
newr := (2*newA^2-2*newA+1)/newA; news := (3*newA^2-3*newA+1)/newA^2;
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 13;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^3 + A^2 + 1)*B - A^2 - A;
QB<B> := ext<QA | modpol>;
r := -A*B + 1; s := 1 - A*B/(B + 1);
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QBz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq b^5*(c^2+c-b)^2/(b^2-b*c-c^3)^2;
u :=
    1
    + w*((3*(A*B-1)+B^2)*c/b
    + w*(((-3*A+1)*B+3)*c/b
    + w*(-2*c/b
    + w*(-3*A*B/b
    + w*(A*(4*B+A+1)/(b*(B+1))
    + w*(A*(A^2+4*A+3)/(b*(B+1))
    + w*(((A^2+4*A+3)*B+3*A+3)*c/(b^2*(B+1))
    + w*((A^2-A-2)*c/(b^2*(B+1))
    + w*(A^2*(A+1)*(3*(A*B-1)*(A+1)+A*B)/(b^2*(B+1)^2)
    + w*(4*A^2*(A+1)^2/(b^2*(B+1)^2)
    + w*(A*(A+1)*(B+A^3-2*A^2-3*A)/(b^2*(B+1)^2)
    + w*(A^3*(B-A^2-A)/(b^2*c*(B+1)^2)
))))))))))));
vB := 
    B
    + w*(A*(A*B-1)/(B+1)
    + w*((-B+A^2+3*A+1)/(B+1)
    + w*(-A*B^2/b
    + w*(A*((A^2+A-1)*B-A-1)/(b*(B+1))
    + w*(-A*(A+2)*B/(b*(B+1))
    + w*((B-A^3-4*A^2-3*A)/(b*(B+1))
    + w*(((-A-1)*B-A^4-2*A^3-A^2)/(b*(B+1))
    + w*(B^2*((A^2+2*A+1)*B+2*A^3+4*A^2+3*A+1)/(b^2*(B+1)^2)
    + w*(A*((A+2)*B-A^2-A)/(b^2*(B+1))
    + w*(-A*(B+A^3-2*A-1)/(b^2*(B+1))
    + w*(-A*(A+1)*(B+A^3-A)/(b^2*(B+1)^2)
    + w*(-A^3*((A+3)*B-A^2+1)/(b^2*c*(B+1)^2)
))))))))))));
denoms := 1/(u*vB);
newA := (
    A*B
    + w*(A*((A+2)*B+1)/(B+1)
    + w*((2*A^2+3*A+1)/(B+1)
    + w*((A+1)^3/(B+1)^2
    + w*(-A*B*((A+1)*B+1)/(b*(B+1))
    + w*(-A*(2*A*B-A-1)/(b*(B+1))
    + w*((B+2*A^3+2*A^2)/(b*(B+1))
    + w*(A+1)*(c/(b^2*(B+1))
    + w*A*(c/(b^2*(B+1))
    + w*(A^2*B/(b^2*(B+1)^2)
    + w*(A*(B+2*(A+1))/(b^2*(B+1)^2)
    + w*((B+(A^3+1))/(b^2*(B+1)^2)
    + w*(-A^2*(B+(A+1))/(b^2*c*(B+1)^2)
))))))))))))) * denoms*u;
newB := denoms*vB^2;
newr := -newA*newB + 1; news := 1 - newA*newB/(newB + 1);
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 14;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^2 + A)*B + A;
QB<B> := ext<QA | modpol>;
r := 1 - (A + B)/((B + 1)*(A + B + 1));
s := (1 - A)/(B + 1);
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QBz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert t eq -(b*(A-1))^3*(A*B+B+1)*(A*B+1)/(c*(A+B)*(B+1)^3*(A+B+1)^2);
u := 
    1
    + w*((2*B-A+3)/(B+1)
    + w*((3*B+A^2+A+3)/(B+1)
    + w*(2*(A+B+1)*(B+A^2+A+1)/(B+1)
    + w*(((3*A+5)*B+A+3)*c/(b*(B+1))
    + w*(-3*(A+B)/(b*(B+1))
    + w*((A+1)*(-2*B-2*A^2+A)/(b*(B+1))
    + w*(-c*(3*B+A)/(b^2*(B+1))
    + w*(c*(-3*B+A^2+4*A)/(b^2*(B+1))
    + w*(-A*((A+1)*B+A^3-A^2+2)/(b^2*(B+1)^2)
    + w*(-A*(A+1)*(2*B-A^2+3)/(b^2*(B+1)^2)
    + w*(-4*A*(A+1)*(B+A^2+A+1)*(A+B+1)/(b^2*(B+1)^2)
    + w*(A*(A+1)*(A-2)*((A+2)*B+(A^3+2*A^2+A+1))/(b^2*(B+1)^2)
    + w*(A*(A+1)*(B^2+B-A^2-A)*c/(b^3*(B+1)^2)
)))))))))))));
vr := 
    b*(2*B+A^2+2*A+1)/(c*(B+1))
    + w*(2
    + w*(-A+3
    + w*(2*(A+B+1)*(B+A^2+A+1)/(B+1)
    + w*(2*(A+B+1)*((A+3)*B-A+1)/(B+1)^2
    + w*(-2*(A+B)/(b*(B+1))
    + w*(-3*(A+B)*(2*B+A^2+1)/(b*(B+1)^2)
    + w*(2*(A-B)*(A+B+1)/(b*(B+1)^2)
    + w*(-c*((A^2+A+2)*B-A^2-3*A)/(b^2*(B+1))
    + w*(2*(A+B)*(B+A^2+A)/(b^2*(B+1))
    + w*(2*A*(A+1)*(B+A^2+A-2)/(b^2*(B+1))
    + w*(-2*A*(A+B+1)*(A+1)*(B+A^2+A+1)/(b^2*(B+1)^2)
    + w*(A*(A+1)*(A-1)*(A+B+1)*(B+A^2+A+1)/(b^2*(B+1)^2)
))))))))))));	// Remark: coefficient is 0 for w^13 so one term less
vs := 
    (1-A)/(B+1)
    + w*(2
    + w*(((A+2)*B-A^2+2)/(B+1)
    + w*(3*(A+B+1)*(B+A^2+A+1)/(B+1)
    + w*(c*((-A^2+A+6)*B-2*A+2)/(b*(B+1))
    + w*(-(A+B)/(b*(B+1))
    + w*(-(A+1)*(3*B+3*A^2+2*A)/(b*(B+1))
    + w*(-c*((A+2)*B-A)/(b^2*(B+1))
    + w*(-c*(2*B+A^2+A)/b^2
    + w*(A*(A+1)*(B+A^2+4*A-4)/(b^2*(B+1)^2)
    + w*(-A*(A+1)*(3*B+2*A^2+1)/(b^2*(B+1)^2)
    + w*(-A*(A+1)^2*(A+B+1)/(b^2*(B+1)^2)
    + w*(-A*(A+1)*(A+B+1)*(2*A+3)*(B+A^2+A+1)/(b^2*(B+1)^2)
    + w*(2*A^2*(A+1)^2*(A+B+1)*((A+1)*B+A^3+2*A^2+A-1)/(b^2*(B+1)^2*c)
)))))))))))));
denom := -1/((vr-u)*(vs-u));
newA := (vr*u-vs^2+vs*u-u^2)*denom;
newB := (vr*vs-2*vr*u+u^2)*denom;
newr := 1 - (newA + newB)/((newB + 1)*(newA + newB + 1));
news := (1 - newA)/(newB + 1);
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 15;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^2 + A + 1)*B + A^2;
QB<B> := ext<QA | modpol>;
r := 1 + (A*B + B^2) / (A^2*(A + B + 1));
s := 1 + B/(A*(A + 1));
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QBz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq b^3*((A^3-B)/(A*B*(A+B+1)))^2;
u :=
    (A+B)*(A+1)/(A*(A+B+1))
    + w*(-3
    + w*(3
    + w*((A+B)*(A+B+1)*(B-2*A)/(A^3-B)
    + w*(-3*(A+B+1)^2*(A+1)*B/(A^3-B)
    + w*(-3*B/(b*A*(A+1))
    + w*(-B*((A+1)*B+A^2-2*A)/(b*(A^3-B))
    + w*(3*A^3*(B+1)/(b*(A^3-B))
    + w*(3*A*B*(A+B+1)^2/(b*(A^3-B))
    + w*(c*A^3*(A+1)*((A+3)*B+A+2)/(b^2*(A^3-B))
    + w*(-3*A^2*B/(b^2*(A^3-B)*(A+1))
    + w*(-3*B^2*(A+B+1)/(b^2*(A^3-B))
    + w*(-3*A^4*(B+1)*B*(A+B+1)/(b^2*(A^3-B)^2)
    + w*(3*A^4*(B+1)*B*(A+B+1)/(b^2*(A^3-B)^2)
)))))))))))));	// Remark: coefficient is 0 for w^14 so one term less
vr :=
    ((A+1)*B+A^2+A+1)/(A+B+1)^2
    + w*(-((A+1)*B+3*A^2)/A^2
    + w*(B+3
    + w*(A*(A+B+1)*((A+1)*B-2*A)/(A^3-B)
    + w*(A^2*(A+B+1)*((A+1)*B+A+2)/(A^3-B)
    + w*(((A^3-A^2+2*A+1)*B+A^3+A^2)/(b*A^3*(A+1))
    + w*(B*((A+1)*B+3*A)/(b*(A^3-B))
    + w*(2*B*(A+B+1)*(B-A)/(b*(A^3-B))
    + w*(2*A*B*(A+B+1)^2/(b*(A^3-B))
    + w*(A^3*(A+B+1)^2*((A^2-A-1)*B+A^2)/(b*(A^3-B)^2)
    + w*(A*((A^3+2*A^2-A+1)*B+A^3+A^2)/(b^2*(A^3-B)*(A+1))
    + w*(-3*B^2*(A+B+1)/(b^2*(A^3-B))
    + w*(-A^2*B*(A+B+1)*((A^2-A-1)*B+A^2)/(b^2*(A^3-B)^2)
    + w*(-A^4*B*(A+B+1)*(A-1)*(B+1)/(b^2*(A^3-B)^2)
    + w*(A^5*(A+B+1)^2*((A+1)*B+A)/(b^2*(A^3-B)^2)
))))))))))))));
vs :=
    (A^3+2*A+1-2*B^2-B)/((A+1)*(A+B+1)^2)
    + w*(-2
    + w*(2
    + w*(B*(A+B+1)*(2*B+3*A^2+4*A+3)/(A^3-B)
    + w*(-2*B*(A+1)*(A+B+1)^2/(A^3-B)
    + w*(B*(A^3-2*A^2-B)/(b*A^3*(A+1))
    + w*(B*((A+1)*B+A^2+3*A)/(b*(A^3-B))
    + w*(-2*A*B*(A+B+1)/(b*(A^3-B))
    + w*(2*A*B*(A+B+1)^2/(b*(A^3-B))
    + w*(-A^5*(A+1)*(A+B+1)*((A-2)*B+A-3)/(b*(A^3-B)^2)
    + w*(-2*A^2*B/(b^2*(A^3-B)*(A+1))
    + w*(-2*B^2*(A+B+1)/(b^2*(A^3-B))
    + w*(-2*A^4*B*(B+1)*(A+B+1)/(b^2*(A^3-B)^2)
    + w*(2*A^4*B*(B+1)*(A+B+1)/(b^2*(A^3-B)^2)
)))))))))))));	// Remark: coefficient is 0 for w^14 so one term less
denom := -1/(u*(vs-u)*(vr-vs)^2);
comfac := (vr*u-vs^2+vs*u-u^2);
newA := u*(vr-vs)*comfac*denom;
newB := (vr*vs-2*vr*u+u^2)*comfac*denom;
newr := 1 + (newA*newB + newB^2) / (newA^2*(newA + newB + 1));
news := 1 + newB/(newA*(newA + 1));
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 16;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^3 + A^2  - A + 1)*B + A^2;
QB<B> := ext<QA | modpol>;
r := (A^2 - A*B + B^2 + B)/(A^2 + A - B - 1);
s := (A - B)/(A + 1);
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq A^9*B^8*(A+1)*(A-1)*(A^2+1)^2/(A^2+2*A-1)^4;
vA :=
      w*(A^4*B^3*(A+B)*(A^2+1)
    - w^2*(A^3*B^2*(A+B)*(A^2+1)
    + w^4*(A*(A+B)*(A^2+2*A-1)
    - w^8*((A^2+2*A-1)^4/(A^3*B^3*(A+B)*(A^2+1))
))));
u := 
     A^5*B^4*(A-1)*(A^2+1)
   + w^8*(A^2+2*A-1)^2;
vB1 :=
      (A-B)/(A^2-2*A-1)^2
     - w*((B - A^2 - A + 1)/((A^2+2*A-1)*(A^2-2*A-1)^2)
     + w^2*((A+1)/(A*B*(A^2-2*A-1)^2)
     + w^2*((B - A^2 - A + 1)/((A^2+2*A-1)*(A^2-2*A-1)^2*b)
     - w^2*(1/(A*B*(A^2-2*A-1)^2*b)
     + w^2*(c*B*(B+1)/((A^2+2*A-1)*(A^2-2*A-1)^2*b^3)
     + w^4*(c^2*B^2*(A+1)*((-A^2 - A + 1)*B - 2*A + 1)/((A^2+2*A-1)^2*(A^2-2*A-1)^2*b^5)
     - w^2*A*(B+1)*c^2/((A^2+2*A-1)*(A^2-2*A-1)^2*b^5)
))))));
vB2 :=
       w*((A^2+2*A-1)/B
     - w^2*(2*A^2*(A*B+1)/(B*b)
     - w^4*(2*A*(A-1)*((A + 1)*B + 1)/(B*b^2)
     - w^2*(c^2*A*B*(A-1)/b^4
     + w^4*(2*c^2*A^2*(A-1)*(A*B + 1)/((A^2+1)*b^5)
     - w^2*2*c^2*A*(A-1)*(A*B + 1)/(B*(A^2+1)*b^5)
)))));
newA := vA/u;
newB := newA + (newA+1)*vB1*vB2;
newr := (newA^2 - newA*newB + newB^2 + newB)/(newA^2 + newA - newB - 1); news := (newA - newB)/(newA + 1);
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 17;
QAB<B> := PolynomialRing(QA);
modpol := B^4 + (A^3 + A^2 - A + 2)*B^3 + (A^3 - 3*A + 1)*B^2 - (A^4 + 2*A)*B + A^3 + A^2;
QB<B> := ext<QA|modpol>;
r := (A^2 + A - B)/(A^2 + A*B + A - B^2 - B);
s := (A + 1)/(A + B + 1);
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq b^4*(A+1)^2*(A^2+A-B)/(c*(B+1)^2*(A^2+A*B+A-B^2-B));
u := 1
     + w*((B^2 + (-2*A^2 + 1)*B - 3*A^3 - 3*A^2 - A)/(A^2*(A+B+1))
     + w*((-B^2 + (3*A + 1)*B + 3*A^2 + 6*A + 2)/((A+1)*(A+B+1))
     + w*(-2*c/b
     + w*(c*(2*B + 3*A + 2)/((A+1)*b)
     + w*(c*(B^3 + (-4*A - 1)*B^2 + (3*A^2 - 2*A - 2)*B + 3*A^3 + 6*A^2 + 2*A)/((A+1)^2*(B-A)*b)
     + w*(-B*(B + 2*A)/((A^2+A-B)*b)
     + w*(c*((3*A + 4)*B - A)/(A*(A+1)*b^2)
     + w*(-3*c*(B+1)/((A+1)*b^2)
     + w*(c^2*(-B^2 + 2*B + 3*A + 3)/((A+1)*(B+1)*b^3)
     + w*(c^2*((-2*A - 3)*B^2 + (A - 3)*B + 2*A^2 + 3*A)/((A+1)*(B-A)*b^3)
     + w*(c^2*(B+1)^2*(4*B + 3*A + 3)/(B*(A+1)^2*b^3)
     + w*(c*(B+1)*(-B^2 + (2*A^2 + 3*A - 1)*B + 3*A^2 + 4*A)/(A*(A+1)^2*(A+B+1)*b^3)
     + w*(c^2*(-B^3 + (-2*A - 2)*B^2 + (-3*A^2 - A - 1)*B + A)/(A^2*(A+1)*(B+1)*b^4)
     + w*(4*c^2*(B+1)^2/((A+1)^2*b^4)
     + w*(c^2*(B+1)^2*(B^2 + (-2*A^2 - A + 1)*B - A)/(A^2*B*(A+1)^2*b^4)
     + w*(-c^3*(B+1)*(A+B+1)/(A*(A+1)^2*b^5)
))))))))))))))));
vr := b/c
     + w*(-((2*A - 1)*B + 3*A)/(A*(B+1))
     + w*(-(-B^2 + (-3*A^2 - 2*A - 1)*B + A)/(A*B*(A+1))
     + w*(-((-A^3 - 5*A^2 - 4*A - 1)*B^2 + (A^3 - 2*A^2 - 3*A - 1)*B + 3*A^4 + 6*A^3 + 4*A^2 + A)/(A*(A+1)*(A^2+A-B))
     + w*(c*(B + 2*A + 2)/(b*(A+1))
     + w*(-c*(B^3 + (A^2 + 2*A + 2)*B^2 + (-2*A^2 + A + 1)*B - 3*A^3 - 3*A^2 - A)/(A*(A+1)*(B-A)*b)
     + w*(-c^2*A*((-A + 2)*B^2 + 2*B - 2*A^2 - 2*A)/((A+1)*(B-A)^2*b^2)
     + w*(c*((2*A^2 + 2*A - 1)*B + A)/(A^2*(A+1)*b^2)
     + w*(-2*c*(B+1)/((A+1)*b^2)
     + w*(2*c*(B+1)^2*(B+A)/(B*(A+1)^2*b^2)
     + w*(-c^2*A*B*(B^3 + (-2*A^3 - 4*A^2 + A + 1)*B^2 + (-2*A^3 - 4*A^2)*B + 2*A^4 + 2*A^3)/((A+1)*(A+B+1)*(B-A)^2*b^3)
     + w*(c^2*(B+1)^2*(A+B+1)*(B + 2*A^2 + A)/(A*B*(A+1)^3*b^3)
     + w*(-c^2*(B+1)^2*((A + 2)*B^2 + (-2*A^2 - A + 2)*B - 2*A^3 - 4*A^2 - 2*A)/(B*(A+1)^3*(B-A)*b^3)
     + w*(-3*c*(B+1)^2/((A+1)^2*b^3)
     + w*(c^2*(B+1)*(3*B + 2)/((A+1)^2*b^4)
     + w*(-c^2*(B+1)*((-A + 1)*B^2 + (-2*A + 1)*B + A^2 - A)/((A+1)^2*(B-A)*b^4)
     + w*(c^3*(A+B+1)*(B^2 + B - A)/((A+1)^2*(B-A)*b^5)
))))))))))))))));
vc := c
      + w*((B^3 + (A^2 + 2*A + 4)*B^2 + (-2*A + 1)*B - A)/(A*B*(A+1)*(B+1))
      + w*((-B^2 + (A - 1)*B + A^2 + 2*A)/((A+1)*(A+B+1))
      + w*(2*c*A*B*(B+1)/(b*(A^2+A*B+A-B^2-B))
      + w*(c*(-2*B + A)/((A+1)*b)
      + w*(c*(B+1)^2*(B^2 + (A^3 + 2*A^2 - A + 1)*B - A^3 - 2*A^2 - A)/(A^2*B*(A+1)^2*b)
      + w*(B^2/((A^2+A-B)*b)
      + w*(c*(-A*B^2 + 2*B - A)/(A*(A+1)*(B+1)*b^2)
      + w*(c*(-B + 1)/((A+1)*b^2)
      + w*(c^2*((-A + 2)*B^2 + 2*B - A^2 - A)/(A*(A+1)*(B+1)*b^3)
      + w*(c^2*((2*A + 1)*B^2 + (3*A + 1)*B - 2*A^2 - A)/((A+1)*(B-A)*b^3)
      + w*(c^2*(B+1)^2*(2*B - A - 1)/(B*(A+1)^2*b^3)
      + w*(c*(B+1)*((A + 2)*B^2 + (A^2 + A + 2)*B - A^3 - 2*A^2 - 2*A)/(A^2*(A+1)^2*(A+B+1)*b^3)
      + w*(c^2*(-B^3 + (2*A - 2)*B^2 + (A^2 + 3*A - 1)*B + A)/(A^2*(A+1)*(B+1)*b^4)
      + w*(2*c^2*B*(B+1)/(A*(A+1)*b^4)
      + w*(c^2*(B+1)^2*(B^2 + (4*A^2 - A + 1)*B - A)/(A^2*B*(A+1)^2*b^4)
      + w*(c^3*(A+B+1)*(-B + 2*A - 1)/(A*(A+1)^2*b^5)
))))))))))))))));
comm := (u + vc - vr)/(u^2*vr + u*vc^2 + 3*u*vc*vr - 2*u*vr^2 + vc^2*vr - 3*vc*vr^2 + vr^3);
newA := -comm*(u*vc + u*vr - vr^2);
newB := comm*(u^2 - 3*u*vr - vc*vr + 2*vr^2);
newr := (newA^2 + newA - newB)/(newA^2 + newA*newB + newA - newB^2 - newB);
news := (newA + 1)/(newA + newB + 1);
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;



N := 18;
QAB<B> := PolynomialRing(QA);
modpol := B^2 + (A^3 - 2*A^2 + 3*A + 1)*B + 2*A;
QB<B> := ext<QA | modpol>;
r := (A^2 - A*B - 3*A + 1)/((A - 1)^2*(A*B + 1));
s := (A^2 - 2*A - B)/(A^2 - A*B - 3*A - B^2 - 2*B);
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
assert w^N eq b^8*(A-1)*(A^2-2*A-B)^5*(A^2*B-2*A*B+2*B+1)^2/((A^2-A*B-3*A-B^2-2*B)^4*(A^2-A*B-3*A+1)^2*c^7);
u :=
    (A^2-A+1)/(A-1)^2
    + w*(3
    + w*(3
    + w*(c*((A+1)*B+2*A^2+1)/(b*A*(A-1))
    + w*(3*c*(B+1)*(A-1)/(b*A)
    + w*(3*A*(A+B)/(b*(A-1)*(A^2-2*A-B))
    + w*(c*(A-B-1)/(b^2*(A-1)^2)
    + w*(3*(B+1)*c/(b^2*(A-1))
    + w*(-3*((A-2)*B-2)*c/(b^2*(A-1))
    + w*(A*(A-B-1)*(A^2*B-2*A*B+2*B+1)/(b^2*(A-1)*(A^2-A*B-3*A-B^2-2*B))
    + w*(3*(A-1)*((A-1)*B-1)/(b^2*(A^2-A*B-3*A+1))
    + w*(3*c*((A-1)*B-1)/(b^3*(A-1))
    + w*(A^2*((A^3-A+1)*B+2*A^2-2*A+1)*(A^2*B-2*A*B+2*B+1)/(b^3*(A-1)^2*(A^2-A*B-3*A-B^2-2*B)*(A^2-A*B-3*A+1))
    + w*(3*A*((A-1)*B-1)/(b^3*(A-1)*(A^2-A*B-3*A+1))
    + w*(3*(A+B+1)*(A^2*B-2*A*B+2*B+1)/(b^3*(A-1)*(A^2-A*B-3*A+1))
    + w*(3*(A+B+1)*c*(A^2*B-2*A*B+2*B+1)/(b^4*(A-1)*(A^2-A*B-3*A+1))
    + w*(3*(A+B+1)*c*(A^2*B-2*A*B+2*B+1)/(b^4*(A-1)*(A^2-A*B-3*A+1))
))))))))))))))));	// Remark: last cof eq 0; cof16 eq cof17
vc := 
    b*((A^2+1)*B+A^2+A+1)/(c*(A^2-A*B-3*A+1))
    + w*(-1
    + w*(((2*A-1)*B+3*A^2-2*A)/(A^2-2*A-B)
    + w*(c*((A+1)*B-2*A^2+4*A+1)/(b*A*(A-1))
    + w*(c*((A+1)*B+3*A+1)/(b*A)
    + w*(-A*(A+B)/(b*(A-1)*(A^2-2*A-B))
    + w*(((A^4-4*A^3+8*A^2-6*A+3)*B+2*A^2-3*A+3)/(b*(A^2-A*B-3*A+1))
    + w*(-c*(B+1)/(b^2*(A-1))
    + w*(-c*((A-2)*B-2)/(b^2*(A-1))
    + w*(A*((-A^3+A^2-1)*B-A^2+A-1)*(A^2*B-2*A*B+2*B+1)/(b^2*(A^2-A*B-3*A-B^2-2*B)*(A^2-A*B-3*A+1))
    + w*(-A^2*(2*B+A+3)*(A^2*B-2*A*B+2*B+1)/(b^2*(A^2-2*A-B)*(A^2-A*B-3*A+1))
    + w*(-c*((A-1)*B-1)/(b^3*(A-1))
    + w*(c*(((A^6-3*A^5+4*A^4-2*A^3+A^2-A+1)*B+2*A^4-2*A^3+1)/(b^3*A*(A^2-A*B-3*A+1)))
    + w*(A*(B+1)*c^2/(b^4*(A^2-2*A-B))
    + w*(A^2*((2*A-1)*B-1)*(A^2*B-2*A*B+2*B+1)/(b^3*(A^2-2*A-B)*(A^2-A*B-3*A+1))
    + w*(-c*((A^2-2*A+2)*B+1)*(A+B+1)/(b^4*(A-1)*(-A*B+A^2-3*A+1))
    + w*(-c*((A^2-2*A+2)*B+1)*(A+B+1)/(b^4*(A-1)*(-A*B+A^2-3*A+1))
))))))))))))))));	// Remark: last cof eq 0; cof16 eq cof17
vr := 
    ((-A^3+A^2-A)*B+A^3-4*A^2+3*A-1)*b/(c*(A-1)*(A^2-A*B-3*A+1))
    + w*(2
    + w*((B+4*A-2)/(A-1)
    + w*(2*c/b
    + w*(2*c*(A-1)*(B+1)/(b*A)
    + w*(2*A*(A+B)/(b*(A-1)*(A^2-2*A-B))
    + w*(((-A^4+A^3-A^2+A-2)*B-2*A^2+2*A-2)/(b*(A^2-A*B-3*A+1))
    + w*(2*c*(B+1)/(b^2*(A-1))
    + w*(-c*A*B*(B+2*A^2-4*A+3)/(b^2*(A^2-2*A-B))
    + w*((A^2*B-2*A*B+2*B+1)*(B+A^3-2*A^2+A+1)/(b^2*(A-1)^2*(A^2-A*B-3*A+1))
    + w*(-A^2*(B-2*A+4)*(A^2*B-2*A*B+2*B+1)/(b^2*(A^2-2*A-B)*(A^2-A*B-3*A+1))
    + w*(2*c*((A-1)*B-1)/(b^3*(A-1))
    + w*(A*B*((-A^2+3*A-2)*B+A-2)/(b^3*(A*B+1)*(A^2-A*B-3*A+1))
    + w*(2*A*((A-1)*B-1)/(b^3*(A-1)*(A^2-A*B-3*A+1))
    + w*(2*A^2*(A^2*B-2*A*B+2*B+1)*((A+1)*B+1)/(b^3*(A^2-2*A-B)*(A^2-A*B-3*A+1))
    + w*(2*c*A^2*(B+1)*(A^2*B-2*A*B+2*B+1)/(b^4*(A^2-2*A-B)*(A^2-A*B-3*A+1))
    + w*(A*B*((-A^2 + 2*A - 1)*B + A - 1)*c/(b^4*(A^2-A*B-3*A+1))
))))))))))))))));	// Remark: last cof eq 0
newA := vc*(u^4 - 5*u^3*vr + u^2*vc^2 + u^2*vc*vr + 10*u^2*vr^2 - 9*u*vr^3 - vc*vr^3 + 3*vr^4)/
	((u*vc + u*vr - vr^2)*(u^2*vr + u*vc^2 + 3*u*vc*vr - 2*u*vr^2 + vc^2*vr - 3*vc*vr^2 + vr^3));
newB := -(u^4*vr + 2*u^3*vc^2 + 4*u^3*vc*vr - 4*u^3*vr^2 - 4*u^2*vc^2*vr - 13*u^2*vc*vr^2 + 6*u^2*vr^3 - u*vc^3*vr + 14*u*vc*vr^3 - 4*u*vr^4 + 2*vc^2*vr^3 - 5*vc*vr^4 + vr^5)
	/(vc*(u*vc + u*vr - vr^2)*(u^2 - 3*u*vr - vc*vr + 2*vr^2));
newr := (newA^2 - newA*newB - 3*newA + 1)/((newA - 1)^2*(newA*newB + 1));
news := (newA^2 - 2*newA - newB)/(newA^2 - newA*newB - 3*newA - newB^2 - 2*newB);
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;


N := 19;
QAB<B> := PolynomialRing(QA);
modpol := B^5 - (A^2 + 2)*B^4 - (2*A^3 + 2*A^2 + 2*A - 1)*B^3 + (A^5 + 3*A^4 + 7*A^3 + 6*A^2 + 2*A)*B^2 - (A^5 + 2*A^4 + 4*A^3 + 3*A^2)*B + A^3 + A^2;
QB<B> := ext<QA | modpol>;
r := 1 + A*(A+B)*(B-1)/((A+1)*(A^2-A*B+2*A-B^2+B));
s := 1 + A*(B-1)/((A+1)*(A-B+1));
b := r*s*(r-1); c := s*(r-1);
E := EllipticCurve([1-c,-b,-b,0,0]);
P := E ! [0,0];
assert N*P eq E ! 0;
QAz<z> := PolynomialRing(QB);
EA, phi := IsogenyFromKernel(E, &*{(z-(n*P)[1]) : n in [1..N-1]});
t := TatePairing(P,-P,N);
Qw<w> := ext<QB | z^N - t>;
F9 := -c^5 - c^4 + c^3*b - c^3 + 3*c^2*b - 3*c*b^2 + b^3;
F10 := c^5 + c^4*b + 3*c^3*b - 3*c^2*b^2 + c^2*b - 2*c*b^2 + b^3;
assert w^N eq  b^7*(F9/((b-c)*F10))^2;
u := 1
    + w*((-2*B^3 + (-A^2 + 4)*B^2 + (7*A^2 + 5*A - 2)*B - 3*A^3 - 9*A^2 - 5*A)/((A-B+1)*(A^2-A*B+2*A-B^2+B))
    + w*((-B^2 - B + 3*A + 2)/(A-B+1)
    + w*(-2*c/b
    + w*(c*((3*A - 1)*B^4 + (3*A^2 - 4*A + 1)*B^3 + (-3*A^4 - 5*A^3 - 6*A^2)*B^2 + (3*A^4 + 2*A^3 + A^2 + 2*A)*B + 3*A^3 + 3*A^2)/(b*A*(A+B)*(A-B+1))
    + w*(A*(b-c)*(2*B^2 + (3*A - 2)*B - 3*A^3 - 5*A^2 - 5*A)/(b^2*A*(A+B)*(A+1)*(A-B+1))
    + w*((b-c)*(-B + 2*A + 3)/(b^2*(A+B))
    + w*((B-1)^2*((A^2 - 2*A - 3)*B^2 + (3*A^3 + 2*A^2 + 2*A + 3)*B + 3*A^2 + 3*A)/(b*(A+B)*(A-B+1)^2)
    + w*(A*(B-1)^2*((A - 3)*B^2 + (-A^3 - A^2 - A + 3)*B + 3*A^2 + 3*A)/(b^2*(A+1)*(A-B+1)^2*(A^2-A*B+2*A-B^2+B))
    + w*((b-c)*((A - 3)*B + 2*A + 3)/(b^3*(A-B+1)*(A+1))
    + w*(-3*A*B*(B-1)^2*(B - A^2 - A - 1)/(b^2*(A-B+1)^2*(A+B))
    + w*(-A*B*(A+1)*(B-1)^2*(B^2 - (A^2 + 3*A + 4)*B + (3*A^2 + 5*A + 3))/(b^2*(A-B+1)^3*(A+B))
    + w*(-B*(B-1)*(A^2-A*B+2*A-B^2+B)*(B^3 - (A^2 - A - 1)*B^2 - (A^2 + 6*A + 5)*B + (2*A^2 + 5*A + 3))/(b^2*(A-B+1)^3*(A+B))
    + w*(B*c*(B-1)^2*((4*A^2 + 7*A + 3)*B + (-3*A^3 - 10*A^2 - 10*A - 3))/(b^3*(A-B+1)^2*(A+B))
    + w*((b-c)*(B-1)*(-B^3 + 4*B^2 + (-2*A^2 + A - 3)*B - 3*A)/(b^4*(A-B+1)^2*(A+B))
    + w*(B*(B-1)^3*(B^3 + (-A^2 - 1)*B^2 + (-A^3 + 2*A^2 + 2*A)*B - 2*A^3 - 5*A^2 - 3*A)/(b^3*(A-B+1)^3*(A+B))
    + w*(4*c*A*(A+1)*(B-1)^3*B/(b^4*(A-B+1)^2*(A+B))
    + w*(c*(b-c)*(-2*B^4 + (-2*A + 1)*B^3 + (3*A^3 + 8*A^2 + 6*A + 1)*B^2 + (-3*A^3 - 5*A^2 - A)*B)/(A*b^5*(A-B+1)*(A+B))
    + w*((b-c)*B*(B-1)*(-B^3 + (A^2 + 1)*B^2 + (A^3 + A)*B - A^3)/(b^5*A*(A-B+1)^2*(A+B))
))))))))))))))))));
vr := b/c
     + w*((B^3 + (4*A + 1)*B^2 + (-A^3 - 4*A - 2)*B - 2*A^3 - 6*A^2 - 3*A)/((A+1)*(A^2-A*B+2*A-B^2+B))
     + w*(3-B
     + w*((A+1)*(B-1)*(-B^3 + (-3*A - 1)*B^2 + (3*A^3 + 4*A^2 + 4*A + 2)*B + 2*A^2 + 2*A)/((A+B)*(A-B+1)^2)
     + w*((b-c)*((-A - 2)*B + 2*A^2 + 3*A + 2)/(b*c*(A+1)*(A-B+1))
     + w*((B-1)*(B^3 + (4*A - 1)*B^2 + (-A^3 - 6*A)*B - 2*A^3 - 4*A^2 + A)/(b*(A-B+1)*(A+1)*(A^2-A*B+2*A-B^2+B))
     + w*((b-c)*(B^3 - B^2 + (-A^3 - 4*A^2 - 3*A)*B + 3*A^3 + 5*A^2 + 2*A)/(b^2*(A-B+1)*A*(A+B))
     + w*((A+1)*(B-1)*((-A - 3)*B^3 + (3*A^2 + 3*A + 6)*B^2 + (-3*A^2 - 3)*B - 2*A)/(b*(A+B)*(A-B+1)^2)
     + w*(2*(b-c)*(B-1)/(b^2*c*(A-B+1))
     + w*((b-c)*(B + 2*A + 2)/(b^3*(A+1)^2)
     + w*((b-c)*(B^4 + (A + 1)*B^3 + (-A^3 - 4*A^2 - 3*A - 2)*B^2 + (A^3 + A^2)*B - A)/(b^3*(A-B+1)*B*(A+B))
     + w*((B-1)^2*((2*A^2 + 2*A)*B^2 + (-2*A^3 - 6*A^2 - 4*A)*B)/(b^2*(A-B+1)^2*(A+B))
     + w*((A+1)*(B-1)*((-2*A - 1)*B^4 + (A^3 + 4*A + 1)*B^3 + (A^3 + 5*A^2 - A)*B^2 + (-2*A^3 - 4*A^2)*B)/(b^2*(A-B+1)^2*A*(A+B))
     + w*(c*B*(B-1)*(-B^4 + (-A + 1)*B^3 + (A^3 + 5*A^2 + 7*A + 2)*B^2 + (-3*A^3 - 10*A^2 - 11*A - 4)*B + 2*A^3 + 6*A^2 + 6*A + 2)/(b^3*(A-B+1)^2*(A+B))
     + w*(((A + 1)*B^4 + (-2*A^3 - 3*A^2)*B^3 + (A^5 + A^4 + A^3 - A^2 - 5*A - 1)*B^2 + (-A^5 + 2*A^2 + 4*A)*B + A^3 - A^2 - 2*A)/(b^3*(A-B+1)^2*(A+1))
     + w*(-3*A*B*(B-1)^3*(A + 1)/(b^3*(A-B+1)^2*(A+B))
     + w*(c*B*(B-1)*(B^4 - B^3 + (A^3 - A)*B^2 + (-3*A^3 - 3*A^2)*B + 2*A^3 + 2*A^2)/(b^4*A*(A+B)*(A-B+1)^2)
     + w*(c*B*(B-1)*(B^4 + (A - 1)*B^3 + (-A^3 - 4*A^2 - 4*A)*B^2 + (A^3 + 4*A^2 + 3*A)*B - A^2 - A)/(b^4*(A+B)*(A-B+1)^2)
     + w*(-B*(b-c)*A^2*(B-1)^2/(b^5*(A-B+1)^2*(A+B))
))))))))))))))))));
vc := c
     + w*((2*B^3 + (-A^2 + 2*A - 4)*B^2 + (-2*A^3 - A^2 - 5*A + 2)*B + A^3 + A^2 + 3*A)/((A-B+1)*(A^2-A*B+2*A-B^2+B))
     + w*((-B^2 + B + A)/(A-B+1)
     + w*(2*(A+1)*(B-1)^2/(A-B+1)
     + w*(c*B*(-B^4 + (A^2 - A + 1)*B^3 + (2*A^3 + A^2 + 2*A)*B^2 + (-A^5 - 2*A^4 - 4*A^3)*B + A^5 + A^4 + 2*A^3)/(b*A*(A+B)*(A-B+1))
     + w*(c^2*(2*B^3 + (3*A - 2)*B^2 + (-2*A^3 - 5*A^2 - 7*A)*B + A^3 + 2*A^2 + 2*A)/(b^2*(A+B)*(A^2-A*B+2*A-B^2+B))
     + w*(B*(B^2 + (-A^2 - A - 1)*B + A^2)/(A*(A-B+1)*b)
     + w*(B*((A^2 - 2)*B^3 + (2*A^3 + A^2 + 2)*B^2 + (A^4 + A^3 + 2*A^2 - 1)*B - A^4 - 2*A^3 + 3*A + 1)/((A-B+1)*(A^2-A*B+2*A-B^2+B)*b)
     + w*(c*B*((-A + 1)*B^3 + (-A^2 + 2*A - 1)*B^2 + (A^4 - 3*A)*B - A^4 + A^3 + A^2 + A)/(A*(A-B+1)*(A+B)*b^2)
     + w*((b-c)*((A^2 + 2*A - 1)*B - 2*A^2 - A + 1)/(b^3*(A-B+1)*(A+1)^2)
     + w*((b-c)*(-B^2 + (A^2 + 2*A + 1)*B - A)/(b^3*(A-B+1)*(A+B))
     + w*(B*(B-1)*(-B^2 + (A^2 - A)*B - A^2)/(b^2*A*(A-B+1))
     + w*(c*B*(-2*B^4 + 5*B^3 + (A^3 + 3*A^2 + A - 5)*B^2 + (-A^3 - 3*A^2 - A + 2)*B + A^2 + A)/(b^3*A*(A+1)*(B-1)*(A-B+1))
     + w*(c*(B-1)^2*((2*A^2 + A - 1)*B^2 + (A^3 + 1)*B)/(b^3*(A-B+1)^2*(A+B))
     + w*(c^2*B*((-A - 3)*B^4 + (-A^2 - 2*A + 4)*B^3 + (A^4 + 5*A^3 + 9*A^2 + 10*A - 1)*B^2 + (-A^4 - 5*A^3 - 5*A^2 - 6*A)*B + A^3 + A)/(b^4*A*(A+B)*(A-B+1))
     + w*(c*A*(2*B^4 + (-A^2 - A - 3)*B^3 - A^3*B^2 + (A^3 + A + 2)*B - A - 1)/(b^4*(A+1)^2*(A-B+1)^2)
     + w*(-2*(b-c)^2*(B-1)/(b^5*c*(A+1)*(A-B+1))
     + w*(c^2*(B-1)*(4*B^4 + (4*A - 5)*B^3 + (-3*A^3 - 10*A^2 - 12*A + 1)*B^2 + (3*A^3 + 7*A^2 + 5*A)*B)/(b^5*(A-B+1)*(A+1)*(A^2-A*B+2*A-B^2+B))
     + w*((b-c)^2*((-A - 3)*B^2 + (2*A^2 + 2*A + 4)*B + A - 1)/(b^6*(A-B+1)*(A+1)*(A+B))
))))))))))))))))));
comm := (u - vr + vc)/((u*vr + u*vc - vr^2)*(u^2*vr - 2*u*vr^2 + 3*u*vr*vc + u*vc^2 + vr^3 - 3*vr^2*vc + vr*vc^2));
newA := comm*(u*vr + u*vc - vr^2)*(u^2 - 3*u*vr + 2*vr^2 - vr*vc);
newB := comm*(u^4 - 5*u^3*vr + 10*u^2*vr^2 + u^2*vr*vc + u^2*vc^2 - 9*u*vr^3 + 3*vr^4 - vr^3*vc);
newr := 1 + newA*(newA+newB)*(newB-1)/((newA+1)*(newA^2-newA*newB+2*newA-newB^2+newB));
news := 1 + newA*(newB-1)/((newA+1)*(newA-newB+1));
newb := newr*news*(newr-1); newc := news*(newr-1);
assert same_j_invars(EA, newb, newc);
"Formulas verified for N equal", N;


