load "richelot_formulae_strategy.m";
load "uvtable.m";
load "comp_attack.m";


a := 110; b := 67;
//a := 216; b:= 137; //"SIKEp434"
//a := 250; b:= 159; //"SIKEp503"
//a := 305; b:= 192; //"SIKEp610"
//a := 372; b:= 239; //"SIKEp751"




p := 2^a*3^b - 1;
Fp2<I> := GF(p, 2);
assert I^2 eq -1;
R<x> := PolynomialRing(Fp2);

E_start := EllipticCurve(x^3 + 6*x^2 + x);

// NAIVE GENERATION OF AUTOMORPHISM 2i
E1728, phi := IsogenyFromKernel(E_start, x);
for iota in Automorphisms(E1728) do
  P := Random(E1728);
  if iota(iota(P)) eq -P then
    two_i := phi*iota*DualIsogeny(phi);
    break;
  end if;
end for;

infty := E_start ! 0;

repeat
  P2 := 3^b*Random(E_start);
until 2^(a-1)*P2 ne infty;
repeat
  Q2 := 3^b*Random(E_start);
until WeilPairing(P2, Q2, 2^a)^(2^(a-1)) ne 1;

repeat
  P3 := 2^a*Random(E_start);
until 3^(b-1)*P3 ne infty;
repeat
  Q3 := 2^a*Random(E_start);
until WeilPairing(P3, Q3, 3^b)^(3^(b-1)) ne 1;

// generate challenge key

Bobskey := Random(3^b);

EB, chain := Pushing3Chain(E_start, P3 + Bobskey*Q3, b);
PB := P2; for c in chain do PB := c(PB); end for;
QB := Q2; for c in chain do QB := c(QB); end for;

skB := []; // DIGITS IN EXPANSION OF BOB'S SECRET KEY
// kappas := []; // CHAIN OF ISOGENIES // is eigenlijk niet nodig, merkwaardig genoeg!

print "If all goes well then the following digits should be found", Intseq(Bobskey, 3);



sk := ComputationalAttack(E_start, P2, Q2, EB, PB, QB, two_i, P3, Q3); 
