load "richelot_formulae.m"; 
load "uvtable.m"; 

function ComputationalAttack(E_start, P2, Q2, EB, PB, QB, two_i,P3, Q3)

  tim := Cputime();
  // gathering the alpha_i, u, v from table

  expdata := [[0, 0, 0] : i in [1..b-3]];
  for i in [1..b-3] do
    if IsOdd(b-i) then
      index := (b - i + 1) div 2;
      exp := uvtable[index][2];
      if exp le a then
        u := uvtable[index][3];
        v := uvtable[index][4];
        expdata[i] := [exp, u, v];
      end if;
    end if;
  end for;

  // gather digits until beta_1

  bet1 := 0;
  repeat
    bet1 +:= 1;
  until expdata[bet1][1] ne 0;

  ai := expdata[bet1][1];
  u := expdata[bet1][2];
  v := expdata[bet1][3];

  print "Determination of first", bet1, "ternary digits. We are working with 2^"*IntegerToString(ai)*"-torsion.";

  bi := b - bet1;
  alp := a - ai;

  for j in CartesianPower([0,1,2], bet1) do
    print "Testing digits", &*[IntegerToString(j[k])*" " : k in [1..bet1]];
    tauhatkernel := 3^bi*P3 + (&+[3^(k-1)*j[k] : k in [1..bet1]])*3^bi*Q3;
    tauhatkernel_distort := u*tauhatkernel + v*two_i(tauhatkernel);
    C, tau_tilde := Pushing3Chain(E_start, tauhatkernel_distort, bet1);
    P_c := u*P2 + v*two_i(P2); for taut in tau_tilde do P_c := taut(P_c); end for;
    Q_c := u*Q2 + v*two_i(Q2); for taut in tau_tilde do Q_c := taut(Q_c); end for;
    tim4 := Cputime();
    split, chain, E1, E2 := Does22ChainSplit(C, EB, 2^alp*P_c, 2^alp*Q_c, 2^alp*PB, 2^alp*QB, ai);
    print "Chain took ", Cputime(tim4), "seconds.";
    if split then
      print "Glue-and-split! The first bet1 digits are determined";
      break;
    end if;
  end for;

  
   //  EB <- E <- E_start
   //  |    |
   //  v    v
   //  C1-> C
   //
   // chain: C x EB -> E x C1

  E, _ := Pushing3Chain(E_start, tauhatkernel, bet1);

  // Computing the 3^b torsion in C 
  P3c := u*P3 + v*two_i(P3); Q3c := u*Q3 + v*two_i(Q3);
  for isog in tau_tilde do P3c := isog(P3c); end for; 
  for isog in tau_tilde do Q3c := isog(Q3c); end for; 
  
  // Determine which curve is C1 or E
  if jInvariant(E2) eq jInvariant(E) then 
    C1 := E1; 
    index := 1;
  else 
    C1 := E2; 
    index := 2; 
  end if;

  function chain_evaluation(c, X) // Evaluates chain on [X,Id(EB)] and outputs the image on C1
    X := [X, Id(EB)];
    tim5 := Cputime();

    for f in c do 
      X := f(X);
    end for;
    print "This took ", Cputime(tim5), "seconds.";
    return X[index]; 
  end function; 
  P3c_CB := C1 ! chain_evaluation(chain, P3c);
  Q3c_CB := C1 ! chain_evaluation(chain, Q3c);
 


  // Generate points of order p+1 on curve C1 which has order (p+1)^2
  p := Characteristic(BaseField(C1)); 
  while true do 
    P := Random(C1); 
    if (((p+1) div 2) * P ne Id(C1)) and (((p+1) div 3) * P ne Id(C1)) then
      P3_CB := ((p+1) div 3^b) * P;
      break;
    end if;
  end while; 

  while true do
    Q := Random(C1);
    if ((p+1) div 2) * Q ne Id(C1) and ((p+1) div 3) * Q ne Id(C1) then
            w := WeilPairing(P, Q, p + 1); 
            if w^((p+1) div 2) ne 1 and w^((p+1) div 3) ne 1 then
                Q3_CB := ((p+1) div 3^b) * Q;
                break; 
            end if; 
    end if;
  end while;


  g := WeilPairing(P3_CB, Q3_CB,3^b); 
  Z3b := Integers(3^b);

  tim1 := Cputime();
  for G in [P3_CB, Q3_CB] do
    xp := fast_log3(WeilPairing(P3c_CB, G, 3^b),g);
    xq := fast_log3(WeilPairing(Q3c_CB, G, 3^b),g);
    if ((xq mod 3) ne 0) then
      sk := Integers() ! (-( Z3b ! xp)/(Z3b ! xq)); 
    end if; 
  end for;
  print "Fast discrete log: ", Cputime(tim1), "seconds.";

  t := Cputime(tim);
  // Check 
  bobscurve, _ := Pushing3Chain(E_start, P3 + sk*Q3, b);
  succes := jInvariant(bobscurve) eq jInvariant(EB);

  if succes then
    print "Bob's secret key = ", sk; 
    print "In total, this took ", t, "seconds.";
  else 
    print "Failed";
  end if; 
  return sk;
 
end function; 

