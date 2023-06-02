function FromProdToJac(C, E, kernel)
  Fp2 := BaseField(C);
  R<x> := PolynomialRing(Fp2);



  P_c2 := C ! kernel[1][1];
  P2 := E ! kernel[1][2];
  Q_c2 := C ! kernel[2][1];
  Q2 := E ! kernel[2][2]; 

  a1 := P_c2[1]; a2 := Q_c2[1]; a3 := (P_c2 + Q_c2)[1]; 
  b1 := P2[1]; b2 := Q2[1]; b3 := (P2 + Q2)[1];

  M := Matrix(Fp2, 3, 3, [a1*b1, a1, b1,
                          a2*b2, a2, b2, 
                          a3*b3, a3, b3]);

  RST := M ^ -1 * Matrix(Fp2, 3, 1, [1,1,1]);
  R := RST[1][1]; S := RST[2][1]; T := RST[3][1];
  
  RD := R * Determinant(M); 
  da := (a1 - a2)*(a2 - a3)*(a3 - a1);
  db := (b1 - b2)*(b2 - b3)*(b3 - b1);

  s1 := - da / RD; t1 := db / RD;
  s2 := -T/R; t2 := -S/R;

  a1_t := (a1 - s2) / s1;
  a2_t := (a2 - s2) / s1;
  a3_t := (a3 - s2) / s1;
  h := s1 * (x^2 - a1_t) * (x^2 - a2_t) * (x^2 - a3_t);

  H := HyperellipticCurve(h);
  J := Jacobian(H);

  function isogeny(pair)
    Pc := pair[1];
    P := pair[2];

    if Pc ne Id(C) then 
      JPc := elt<J|s1 * x^2 + s2 - Pc[1], Pc[2] / s1>; 
    end if; 

    if P ne Id(E) then
      JP := elt<J|(P[1]-t2)*x^2 - t1, P[2]*x^3 / t1>; 
    end if; 

    if (Pc ne Id(C)) and (P ne Id(E)) then
      return JPc + JP; 
    end if; 

    if Pc ne Id(C) then 
      return JPc; 
    end if; 

    if P ne Id(E) then 
      return JP; 
    end if;
  end function;

  

  return h, isogeny;
end function; 

function FromJacToJac(h, kernel)
  R<x> := Parent(h);
  Fp2 := BaseRing(R);

  J := Jacobian(HyperellipticCurve(h));

  G1 := kernel[1];
  G2 := kernel[2];
  G3 := h div (G1*G2);
  assert h mod (G1*G2) eq 0;
  assert (Coefficient(G1,2) eq 1) and (Coefficient(G2,2) eq 1);

  delta := Matrix(Fp2, 3, 3, [Coefficient(G1, 0), Coefficient(G1, 1), Coefficient(G1, 2),
                              Coefficient(G2, 0), Coefficient(G2, 1), Coefficient(G2, 2),
                              Coefficient(G3, 0), Coefficient(G3, 1), Coefficient(G3, 2)]);
  delta := Determinant(delta)^(-1);

  H1 := delta*(Derivative(G2)*G3 - G2*Derivative(G3));
  H2 := delta*(Derivative(G3)*G1 - G3*Derivative(G1));
  H3 := delta*(Derivative(G1)*G2 - G1*Derivative(G2));

  hnew := H1*H2*H3;
  Jnew := Jacobian(HyperellipticCurve(hnew));
 

  function isogeny(D)
    Du := D[1]; Dv := D[2];
    
   
    if not IsMonic(Du) then
      Du := Du div Coefficient(Du, 2);
    end if;
    Dv := Dv mod Du; 

    s := -Coefficient(Du, 1); p := Coefficient(Du,0);
    g1red := G1 - Du; 
    g2red := G2 - Du; 
    assert (Coefficient(g1red,2) eq 0) and (Coefficient(g2red,2) eq 0);
    g11 := Coefficient(g1red,1); g10 := Coefficient(g1red,0);
    g21 := Coefficient(g2red,1); g20 := Coefficient(g2red,0);

    Px := (g11*g11*p + g11*g10*s + g10*g10) * H1*H1
           + (2*g11*g21*p + (g11*g20+g21*g10)*s + 2*g10*g20) * H1*H2 
           + (g21*g21*p + g21*g20*s + g20*g20) * H2*H2;


    assert Coefficient(Dv, 2) eq 0;
    v0 := Coefficient(Dv, 0);
    v1 := Coefficient(Dv, 1);

    Py2 := v1*v1*p + v1*v0*s + v0*v0;

    Py1 := (2*v1*g11*p + v1*g10*s + v0*g11*s + 2*v0*g10)*x
          - (v1*g11*s*p + 2*v1*g10*p + v0*g11*(s*s-2*p) + v0*g10*s);
    Py1 := Py1 * H1;

    Py0 := H1*H1 * Du * (g11*g11*p + g11*g10*s + g10*g10);
    _, Py1inv, _ := XGCD(Py1,Px);
    Py := (-Py1inv * (Py2 * hnew + Py0)) mod Px;
    

    
    
    assert Degree(Px) eq 4;
    assert Degree(Py) le 3; 

    Dx := (hnew - Py^2) div Px;
    Dy := (-Py) mod Dx;
    Dx := Dx div Coefficient(Dx, 2);
    //assert (Dy^2-hnew) mod Dx eq 0;

    
    return [Dx,Dy];
  end function; 
  
  

  return hnew, isogeny;
end function;

function FromJacToProd(G1,G2,G3)
  h := G1*G2*G3; 
  R<x> := Parent(h);
  Fp2 := BaseRing(R);
  M := Matrix(Fp2, 3, 3, [Coefficient(G1, 0), Coefficient(G1, 1), Coefficient(G1, 2),
                              Coefficient(G2, 0), Coefficient(G2, 1), Coefficient(G2, 2),
                              Coefficient(G3, 0), Coefficient(G3, 1), Coefficient(G3, 2)]);
  // Find homography
  kernel, _ := KernelMatrix(Transpose(M));  // generators of right kernel

  u := kernel[1][1]; v := kernel[1][2]; w := kernel[1][3]; 
  d := u/2;
  roots := Roots(x^2 - v*x + w*d/2);
  ad := roots[1][1]; b := roots[2][1]; 
  a := ad/d;
  
  // Apply transform G(x) -> G((a*x+b)/(x+d))*(x+d)^2
    // The coefficients of x^2 are H2 := M * (1, a, a^2) 
    // The coefficients of 1 are H0 := M * (d^2, b*d, b^2)

  H2 := M * Matrix(Fp2, 3, 1, [1,a,a*a]); 
  H0 := M * Matrix(Fp2, 3, 1, [d*d, b*d, b*b]);

  H12 := H2[1][1]; H22 := H2[2][1]; H32 := H2[3][1]; 
  H10 := H0[1][1]; H20 := H0[2][1]; H30 := H0[3][1]; 
 
  assert Evaluate(G1,(a*x+b)/(x+d))*(x+d)^2 eq H12*x^2+H10; 

  h2 := (H12*x^2+H10)*(H22*x^2+H20)*(H32*x^2+H30); 

  p1 := (H12*x+H10)*(H22*x+H20)*(H32*x+H30);
  p2 := (H12+H10*x)*(H22+H20*x)*(H32+H30*x);

  E1 := EllipticCurve((x + H10*H22*H32)*(x + H20*H12*H32)*(x + H30*H12*H22));
  E2 := EllipticCurve((x + H12*H20*H30)*(x + H22*H10*H30)*(x + H32*H10*H20));

  function isogeny(D)
    J := Jacobian(HyperellipticCurve(h)); 
    D := elt<J| D[1], D[2]>; 
    U := D[1]; V := D[2];
 
    // Apply homography to the mumford coordinates
    //  H' -> H : (x,y) -> (ax+b/cx+d, y/(cx+d)³)

    U_ := Coefficient(U,0) * (x+d)^2 + Coefficient(U,1)*(a*x+b)*(x+d) + Coefficient(U,2)*(a*x+b)^2;
    V_ := Coefficient(V,0) * (x+d)^3 + Coefficient(V,1)*(a*x+b)*(x+d)^2;
    V_ := V_ mod U_ ;
    v1 := Coefficient(V_,1); v0 := Coefficient(V_,0);
    
    s := - Coefficient(U_,1) / Coefficient(U_,2);
    p := Coefficient(U_,0) / Coefficient(U_,2); 
    
    // Map to E1 
    // H'-> E1 : (x,y) -> (x², y)
    U1 := x^2 - (s*s - 2*p)*x + p^2; 
    V1 := (p1 - v1^2 * x + v0^2) / (2*v0);
    // Reduction to E1
    V1 := V1 mod U1;
    U1red := (p1 - V1^2) div U1;
    xP1 := -Coefficient(U1red,0) / Coefficient(U1red,1) ;
    yP1 := Evaluate(V1,xP1);
    assert yP1^2 eq Evaluate(p1,xP1);


    // Map to E2
    // H' -> E2 : (x,y) -> (1/x², x/y³)
    U2 := x^2 - ((s*s-2*p)/p^2)*x + 1/p^2;

    V21 := x^2 * (v1 * (s*s-2*p) + v0*s);
    V20 := p2 + x^4 * (p*(v1^2*p + v1*v0*s + v0^2));

    _, V21inv, _ := XGCD(V21,U2);
    V2 := (V21inv * V20) mod U2;
    assert V2^2 mod U2 eq p2 mod U2; 

    U2red := (p2 - V2^2) div U2;
    xP2 := -Coefficient(U2red,0) / Coefficient(U2red,1);
    yP2 := Evaluate(V2,xP2);
    assert yP2^2 eq Evaluate(p2,xP2);


    return [E1 ! [H12*H22*H32*xP1, H12*H22*H32*yP1], E2 ! [H10*H20*H30*xP2, H10*H20*H30*yP2]];
  end function; 
  return isogeny, E1, E2; 
end function;


function Does22ChainSplitSpeedup(C, E, kernel, n)
    // Compute (2^n,2^n)-chain with domain CxE
    // kernel := [[Pc, P], [Qc, Q]]
    chain := []; 
    Fp2 := BaseField(C);

    // Glue step 
    kernelglue := [[(2^(n-1))*(C ! kernel[1][1]),(2^(n-1))*(E ! kernel[1][2])],[(2^(n-1))*(C ! kernel[2][1]),(2^(n-1))*(E ! kernel[2][2])]];
    h, f := FromProdToJac(C,E,kernelglue);
    chain cat:= [f];
    
    image1 := f(kernel[1]); image2 := f(kernel[2]);  
    pos := 1;
    kernel_aux := [[image1[1],image1[2]],[image2[1],image2[2]]];
    indices := [0];
    //JacToJac step
    for i := 1 to n-2 do
        //print indices;
        gap := n-1-i - indices[pos];
        //print "gap: ", gap;
        if gap eq 0 then
            // print "no aux computation";
            // print "compute 2^i with i = ", n-i-1;
            kernel := kernel_aux[[2*pos-1,2*pos]];
            kernel := [kernel[1][1],kernel[2][1]]; //only u(x) needed
            // print "as 1*", kernel_aux[2*pos-1];
            if not indices[pos] eq 0 then
                    Prune(~indices);
                    Prune(~kernel_aux);
                    Prune(~kernel_aux);
                    pos -:= 1;
            end if;

    
        elif gap eq 1 then
            // print "no aux computation";
            // print "compute 2^i with i = ", n-i-1;
            // print "as 2*", kernel_aux[2*pos-1];
            kernel := kernel_aux[[2*pos-1,2*pos]];
            
            u1, _ := JacobianDoubles(h,kernel[1][1],kernel[1][2],1);
            u2, _ := JacobianDoubles(h,kernel[2][1],kernel[2][2],1);
            
            kernel := [u1, u2];
           
            if not indices[pos] eq 0 then
                    Prune(~indices);
                    Prune(~kernel_aux);
                    Prune(~kernel_aux);
                    pos -:= 1;
            end if;    
        else
            // Compute auxiliary points
            new_ind := indices[pos] + Floor(1*gap/2);
            new_aux := kernel_aux[[2*pos-1,2*pos]];
            
            e := Floor(1*gap/2);
            u1, v1 := JacobianDoubles(h,new_aux[1][1],new_aux[1][2], e);
            u2, v2 := JacobianDoubles(h,new_aux[2][1],new_aux[2][2], e);
            new_aux := [[u1,v1], [u2,v2]];
           

            Append(~indices, new_ind);
            kernel_aux cat:=  new_aux;
            pos +:= 1;
               
            // Compute current kernel
            e := Ceiling(1*gap/2);
            
            u1, _  := JacobianDoubles(h,new_aux[1][1],new_aux[1][2],e); 
            u2, _  := JacobianDoubles(h,new_aux[2][1],new_aux[2][2],e);
            kernel := [u1,u2];
        end if;
        
        h, f := FromJacToJac(h,kernel);
        
        chain cat:= [f];
        // Push all points through the isogeny
        images := [];
        // timer := Cputime();
        for j in [1..#kernel_aux] do
            image := f(kernel_aux[j]);
            images cat:= [image];
        end for;
        kernel_aux := images;
        // print "Pushing points through took: ", Cputime(timer), "seconds";
  end for;

  G1 := kernel_aux[1][1];
  G2 := kernel_aux[2][1];
  G3 := h div (G1*G2);
  // print G1, G2, G3;
  delta := Matrix(Fp2, 3, 3, [Coefficient(G1, 0), Coefficient(G1, 1), Coefficient(G1, 2),
                              Coefficient(G2, 0), Coefficient(G2, 1), Coefficient(G2, 2),
                              Coefficient(G3, 0), Coefficient(G3, 1), Coefficient(G3, 2)]);
  delta := Determinant(delta);
  
  if delta ne 0 then
    return false,0, 0, 0;
  end if; 
  tim3 := Cputime();
  f, E1, E2 := FromJacToProd(G1, G2, G3);
  print "Split step takes, " ,Cputime(tim3), "seconds";
  chain cat:= [f];
  return true, chain, E1, E2; 
end function; 




function Pushing3Chain(E, P, i) // compute chain of isogenies quotienting out a point P of order 3^i
  Fp2 := BaseField(E);
  R<x> := PolynomialRing(Fp2);
  chain := [];
  C := E;
  remainingker := P;
  for j in [1..i] do
    kerpol := x - (3^(i-j)*remainingker)[1];
    C, comp := IsogenyFromKernel(C, kerpol);
    remainingker := comp(remainingker);
    chain cat:=[comp];
  end for;
  return C, chain;
end function;



function JacobianDouble(h,u,v)
  assert Degree(u) eq 2;

  q, r := Quotrem(u,2*v);
  if Coefficient(r,0) eq 0 then
    a := q^2;
    b := (v + (h - v^2) div v) mod a;
    return a, b;
  else 
    h3 := 1 / (-Coefficient(r,0)) * q;
    a := u*u;
    b := (v + h3 * (h - v^2)) mod a;

    Dx := (h - b^2) div a;
    Dy := (-b) mod Dx;
    return Dx, Dy;
  end if;
end function;

function JacobianDoubles(h,u,v,n)
  for i in [1..n] do
    u, v := JacobianDouble(h,u,v);
  end for;
  if Coefficient(u,2) ne 1 then
    u := u div Coefficient(u,2);
  end if;
  return u, v; 
end function;

function fast_log3(x,base)
  Fp2 := Parent(x);
  powers := [base];
  bs := base;
  for i:= 0 to 10000 do
    bs := bs^3; 
    if bs eq (Fp2 ! 1) then 
      log_order := i +1;
      break;
    end if;
    Append(~powers,bs);
  end for;
  if not bs eq (Fp2 ! 1) then
    print "Not possible :(";
  end if;

  digits := [];
  for i := 0 to log_order-1 do
    for d := 0 to 2 do
      if (x * powers[i+1]^d)^(3^(log_order-i-1)) eq 1 then
        Append(~digits, (-d) mod 3);
        if not d eq 0 then
          x := x / powers[i+1]^(3-d);
        end if;
        break;
      end if;
    end for;
    if x eq 1 then
      break;
    end if;
  end for;
  dlog := &+[digits[i+1]*3^i: i in [0..#digits-1]]; 
  return dlog;
end function;

