load "richelot_aux_strategy.m"; 
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
    split, chain, E1, E2 := Does22ChainSplitSpeedup(C, EB, [[2^alp*P_c,2^alp*PB],[2^alp*Q_c,2^alp*QB]], ai);//Does22ChainSplit(C, EB, 2^alp*P_c, 2^alp*Q_c, 2^alp*PB, 2^alp*QB, ai);
    print "Chain took ", Cputime(tim4), "seconds.";
    if split then
      print "Glue-and-split! The first bet1 digits are determined";
      break;
    end if;
  end for;

  
   //  EB <- Eguess <- E_start
   //  |    |
   //  v    v
   //  CB-> C

  Eguess, _ := Pushing3Chain(E_start, tauhatkernel, bet1);

  // Computing the 3^b torsion in C 
  P3c := u*P3 + v*two_i(P3); Q3c := u*Q3 + v*two_i(Q3);
  for isog in tau_tilde do P3c := isog(P3c); end for; 
  for isog in tau_tilde do Q3c := isog(Q3c); end for; 
  
  if jInvariant(E2) eq jInvariant(Eguess) then 
    CB := E1; 
    index := 1;
  else 
    CB := E2; 
    index := 2; 
  end if;
  function apply_chain(c, X)
    X := [X, Id(EB)];
    tim5 := Cputime();

    for f in c do 
      X := f(X);
    end for;
    print "This took ", Cputime(tim5), "seconds.";
    return X[index]; 
  end function; 
  P3c_CB := CB ! apply_chain(chain, P3c);
  Q3c_CB := CB ! apply_chain(chain, Q3c);
 


  // Generate points of order p+1 on curve CB which has order (p+1)^2
  p := Characteristic(BaseField(CB)); 
  while true do 
    P := Random(CB); 
    if (((p+1) div 2) * P ne Id(CB)) and (((p+1) div 3) * P ne Id(CB)) then
      P3_CB := ((p+1) div 3^b) * P;
      break;
    end if;
  end while; 

  while true do
    Q := Random(CB);
    if ((p+1) div 2) * Q ne Id(CB) and ((p+1) div 3) * Q ne Id(CB) then
            w := WeilPairing(P, Q, p + 1); 
            if w^((p+1) div 2) ne 1 and w^((p+1) div 3) ne 1 then
                Q3_CB := ((p+1) div 3^b) * Q;
                break; 
            end if; 
    end if;
  end while;


  g := WeilPairing(P3_CB, Q3_CB,3^b); 
  Z3b := Integers(3^b);

  tim10 := Cputime();
  for G in [P3_CB, Q3_CB] do
    tim10 := Cputime();
    xp := fast_log3(WeilPairing(P3c_CB, G, 3^b),g);
    print "discrete log duurde ", Cputime(tim10), "seconds.";
    xq := fast_log3(WeilPairing(Q3c_CB, G, 3^b),g);
    if ((xq mod 3) ne 0) then
      sk := Integers() ! (-( Z3b ! xp)/(Z3b ! xq)); 
    end if; 
  end for;
  

  t := Cputime(tim);
  // Check 
  bobscurve, _ := Pushing3Chain(E_start, P3 + sk*Q3, b);
  succes := jInvariant(bobscurve) eq jInvariant(EB);

  if succes then
    print "Bob's secret key = ", sk; 
    print "This took ", t, "seconds.";
  else 
    print "Failed";
  end if; 
  return sk;
 
end function; 

