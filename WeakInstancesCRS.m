/*
* Author: Robbe Vermeiren 
* Accompanying code for my thesis about "Cryptanalysis of an isogeny-based system and its applications" 
*/


load "richelot_formulae.m"; 

function GeneratePoint(E,p,order)
    /*
    * INPUT:  - E     = elliptic curve
    *         - p     = integer that divides order
    *         - order = order of E
    *        
    * OUTPUT: - P     = point of order p on E
    */
    // Return point with order p on E
    repeat 
        P := (order div p)*Random(E); 
    until P ne (E ! 0);
    return P; 
end function;

function Pushing2Chain(E, P, i) // compute chain of isogenies quotienting out a point P of order 2^i
    /*
    * INPUT:  - E     = elliptic curve
    *         - P     = point of order 2^i on E
    *         - i     = integer
    *        
    * OUTPUT: - C     = codomain curve isomorphic to E/<P> 
              - chain = 2^i isogeny
    */
  Fp := BaseField(E);
  R<x> := PolynomialRing(Fp);
  chain := [];
  C := E;
  remainingker := P;
  for j in [1..i] do
    kerpol := x - (2^(i-j)*remainingker)[1];
    C, comp := IsogenyFromKernel(C, kerpol);
    remainingker := comp(remainingker);
    chain cat:=[comp];
  end for;
  return C, chain;
end function;

function EvaluateDualIsogeny(chain,P)
    /*
    * INPUT:  - chain = isogeny
    *         - P     = Point in codomain of chain
    *         
    *        
    * OUTPUT: - P     = evaluation of P under the dual of chain
    */
    P1 := P; 
  for i := #chain to 1 by -1 do
    P1 := DualIsogeny(chain[i])(P1);
  end for;
  return P1; 
end function;

function EvaluateIsogeny(chain,P)
  for isog in chain do
    P := isog(P);
  end for;
  return P; 
end function;



// Setup
p := 2^30*167133741769 + 1;
Fp := GF(p); R<x> := PolynomialRing(Fp);
E1 := EllipticCurve([Fp ! 106960359001385152381,Fp ! 100704579394236675333]);

m := 2^15; 


//////////////////////////////////// ATTACK ////////////////////////////////

function ActionOnTorsion(d,isogeny,E2) 
    /*
    * INPUT:  - d       = degree of isogeny
    *         - isogeny = secret isogeny 
    *         - E2      = codomain of isogeny
    *        
    * OUTPUT: - Q01,R01 = generators of E1[m]
              - Q02,R02 = generators of E2[m] where Q02 = isogeny(Q01) and R02 = isogeny(R01)
              
                            
    NOTE: we give the secret isogeny as input to check if we have the correct mu(line 118)
    */


    // Generators of E[2^30]
    repeat
    P1 := (#E1 div m^2)*Random(E1);
    until (m^2 div 2)*P1 ne (E1 ! 0);

    repeat
    P2 := (#E2 div m^2)*Random(E2);
    until (m^2 div 2)*P2 ne (E2 ! 0);

    Z_230 := Integers(m^2);
    // Discrete logarithm to find mu
    f1 := ReducedTatePairing(P1,P1, m^2);
    f2 := ReducedTatePairing(P2,P2, m^2);

    y := Z_230 ! Log(f1,f2);
    mu2 := (y)/d;
    sq, mu := IsSquare(mu2);
    muOptions := [mu, -mu, (2^29+1)*mu , (2^29-1)*mu ];

    // Points of order m^2 
    Q1 := (Integers() ! mu)*P1;
    Q2 := P2; 

    // CHECK
    Q2check := Q1;
    for f in isogeny do Q2check := f(Q2check); end for; 
    assert Q2check eq Q2; // Wrong guess, try again 


    // De Feo's reduction
    kerphi1 :=  m*Q1; 
    kerphi2 :=  m*Q2;

    E01, psi1 := Pushing2Chain(E1, kerphi1, 15);
    E02, psi2 := Pushing2Chain(E2, kerphi2, 15); 

    Q01 := Q1; Q02:= Q2; 
    for isog in psi1 do Q01 := isog(Q01); end for;
    for isog in psi2 do Q02 := isog(Q02); end for;


    ord := #E01;
    repeat 
    R01 := (ord div m^2)*Random(E01);
    until ((WeilPairing(E01 ! Q01, R01, m))^(2^14) ne 1); 

    repeat 
    R02 := (ord div m^2)*Random(E02);
    until ((WeilPairing(E02 ! Q02, R02, m))^(2^14) ne 1); 

    // Push points through dualisogeny to make R a generator of it's kernel
    // psi1
    Q01d := EvaluateDualIsogeny(psi1,Q01); 
    R01d := EvaluateDualIsogeny(psi1,R01); 

    k := Log(Q01d,R01d);
    R01 := R01 - k*Q01;
    // psi2
    Q02d := EvaluateDualIsogeny(psi2,Q02); 
    R02d := EvaluateDualIsogeny(psi2,R02); 

    k := Log(Q02d,R02d);
    R02 := R02 - k*Q02;

    assert EvaluateDualIsogeny(psi1,R01) eq (E1 ! 0);
    assert EvaluateDualIsogeny(psi2,R02) eq (E2 ! 0);

    g1 := WeilPairing(Q01,R01,m); g2 := WeilPairing(Q02,R02,m);

    lambda_d := Log(g1,g2);
    lambda := (Integers(m) ! lambda_d)/(Integers(m) ! d); lambda_inverse := Integers() ! (lambda^(-1)); 

    R02 := lambda_inverse*R02;
    return Q01,R01,Q02, R02;
end function;


function example1()
    /*
        Example1 corresponding to section 5.2
    */
    d := 5*7*19*23;
    // d = 5*7*19*23 en dan 2^14 - d = 33^2
    Enew := E1;
    isogeny := [];
    for p in Factorization(d) do
        P := GeneratePoint(Enew, p[1], #Enew);
        kerpol := &*[(x-(k*P)[1]): k in [1..(p[1]-1)/2]];
        Enew, f := IsogenyFromKernel(Enew, kerpol);
        isogeny cat:= [f];
    end for;
    E2 := Enew;

    P1, Q1, P2, Q2 := ActionOnTorsion(d,isogeny,E2);
    // We have the action of phi on two points of E[2^15]: phi0(P1) = P2
    //                                                     phi0(Q1) = Q2
    // This example concerns 2^14 - d = 33^2; 
    // So let's construct a map: E01 x E02 -> E01 x E02: (33   phi_dual)
    //                                                   (-phi   33    )
    //                           ker := <(33P,phi0(P)), (33Q,phi0(Q))>  with <P,Q> = E[2^14]

    
    split, chain, E3, E4 := Does22ChainSplit(E01, E02, 33*2*P1, 33*2*Q1, 2*P2, 2*Q2, 14);

    if jInvariant(E3) eq jInvariant(E01) then
    index := 2;
    else 
    index := 1;
    end if;

    return chain,index,d;
end function;

function example2()
    /*
        Example2 corresponding to section 5.3
    */

    d := 5^2*7*11^2*19*23*29; 

    // d = 5^2*7*11^2*19*23*29, thus 2^28 - d = 291^2
    Enew := E1;
    isogeny := [];
    for p in Factorization(d) do
        for m in [1..p[2]] do 
            P := GeneratePoint(Enew, p[1], #Enew);
            kerpol := &*[(x-(k*P)[1]): k in [1..(p[1]-1)/2]];
            Enew, f := IsogenyFromKernel(Enew, kerpol);
            isogeny cat:= [f];
        end for;
    end for;
    E2 := Enew;

    P1, Q1, P2, Q2 := ActionOnTorsion(d,isogeny,E2);
    // Now we have the action of phi on two points of E[2^15]: phi0(Q01) = Q02
    //                                                         phi0(R01) = lambda^-1 * R02
    // This example concerns 2^28 - d = 291^2; 
    // So let's construct a map: E01 x E02 -> E01 x E02: (291   phi_dual)
    //                                                   (-phi   291    )
    //                           ker := <(291P,phi0(P)), (291Q,phi0(Q))>  with <P,Q> = E[2^28]
    // We don't know the action on 2^28 torsion, however we can determine the first 14 steps in our chain
    // (since we know the action on 2^14 torsion)
    //
    //            (1)           (2)
    // E01 x E02 -----> Jac(H) -----> E01 x E02


    P1 := 2*P1; Q1 := 2*Q1; // generators of 2^14-torsion
    P2 := 2*P2; Q2 := 2*Q2;

    // Construct (1)
    chain1 := [];
    h1, D11, D12, D21, D22, f := FromProdToJac(E01, E02, 291*P1, 291*Q1, P2, Q2, 14); //glue step
    chain1 cat:= [f];

    // 13 normal steps
    for i in [1..13] do
        h1, D11, D12, D21, D22,f := FromJacToJac(h1, D11, D12, D21, D22, 14-i); 
        chain1 cat:= [f];
    end for;

    // Construct dual of (2)
    dualchain2 := [];
    h2, D11, D12, D21, D22, f := FromProdToJac(E01, E02, 291*P1, 291*Q1, -P2,-Q2, 14); //glue step
    dualchain2 cat:= [f];

    // 13 normal steps
    for i in [1..13] do
        h2, D11, D12, D21, D22,f := FromJacToJac(h2, D11, D12, D21, D22, 14-i); 
        dualchain2 cat:= [f];
    end for;

    H1 := HyperellipticCurve(h1);
    H2 := HyperellipticCurve(h2);

    J1 := Jacobian(H1);
    J2 := Jacobian(H2);
    check, isom := IsIsomorphic(H2,H1);
    assert check; 



    // Now we have the dual of (2), we can determine the kernel of (2)

    R2 := EvaluateIsogeny(dualchain2,[Id(E01),P2]); R2 := J2 ! R2; 
    S2 := EvaluateIsogeny(dualchain2,[Q1,Id(E02)]); S2 := J2 ! S2;

    // Map images from Jac(h2) to Jac(h1)
    function JacobianMap(D)
    xcoord := Roots(D[1]); 
    ycoord1 := Evaluate(D[2], xcoord[1][1]); ycoord2 := Evaluate(D[2], xcoord[2][1]);

    P := H2 ! [xcoord[1][1],ycoord1]; 
    Q := H2 ! [xcoord[2][1], ycoord2];

    imP := isom(P); 
    imQ := isom(Q);

    infty := PointsAtInfinity(H1);
    return (imP - infty[1]) + (imQ - infty[2]); // return divisor on J_1 (P + Q -infty1 - infty2)
    end function;

    R1 := JacobianMap(R2);
    S1 := JacobianMap(S2);





    // With this kernel, we determine (2) 
    chain2 := [];
    // 13 normal steps
    D11 := R1[1]; D12 := R1[2]; D21 := S1[1]; D22 := S1[2];
    for i in [0..12] do
        h1, D11, D12, D21, D22,f := FromJacToJac(h1, D11, D12, D21, D22, 14-i); 
        chain2 cat:= [f];
    end for;

    // split step
    G1 := D11 div Coefficient(D11,2);
    G2 := D21 div Coefficient(D21,2);
    G3 := h1 div (G1*G2);


    f, E3, E4 := FromJacToProd(G1, G2, G3);
    chain2 cat:= [f];

    // composition of (1) and (2)
    chain := chain1 cat chain2;


    if jInvariant(E3) eq jInvariant(E01) then
    index := 2;
    else 
    index := 1;
    end if;

    return chain,index,d;
end function;




// Uncomment the example that you want to run
chain,index,d := example1();
//chain,index,d := example2();




// With this map 'chain', we can recover our secret isogeny
// We need to recover the secret exponents as in the context of CRS (Rational/Non-rational map): 
// phi is degree d isogeny that consists of phi5, phi7, phi19, phi23
// For each prime we determine which 'direction' is taken

F := Factorization(d);
secret_exp := []; 

for i in [1..#F] do
// generate point P in the rational p-torsion of E0
P := GeneratePoint(E01,F[i][1],ord);
X := [P, Id(E02)];
X := EvaluateIsogeny(chain,X);
if X[index] eq (Id(E02)) then 
    secret_exp[i] := 0;
else 
    secret_exp[i] := 1;
end if;
end for;

print "These are the secret exponents (0 is rational): ", secret_exp;
