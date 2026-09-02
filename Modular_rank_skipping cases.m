// ============================================================
// Negative curves on blowups of weighted projective planes
// HPC VERSION WITH MODULAR RANK PRETEST
// ============================================================

SetIgnorePrompt(true);

MODULAR_PRIMES := [1000003, 1000033, 1000037];


// ============================================================
// Contribution
// ============================================================

function Contribution(r,LL)
    QQ := Rationals();
    Poly<t> := PolynomialRing(QQ);

    L := [Integers() | i : i in LL];
    pi := &*[(1-t^i) : i in L];
    A := (1-t^r) div (1-t);
    G := GCD(pi,A);
    dG := Degree(G);

    B := Poly!(A div G);
    dB := Degree(B);

    uu,be,cc := XGCD(pi,B);
    dbe := Degree(be);

    R<[v]> := PolynomialRing(QQ,dG+2);
    va := R.(dG+2);

    bnew := &+[Coefficient(be,i)*va^i : i in [0..dbe]];
    RR := &+[v[i]*va^(i-1) : i in [1..dG+1]];
    Bnew := &+[Coefficient(B,i)*va^i : i in [0..dB]];
    AA := bnew-RR*Bnew;

    S := [Coefficient(AA,va,0)]
         cat [Coefficient(AA,va,r-i) : i in [1..r-1]];

    empty := [];

    for a in L do
        dd := GCD(a,r);
        tt := r div dd;
        relations := empty cat
            [&+[S[dd*l+i] : l in [0..tt-1]] : i in [1..dd]];
        empty := relations;
    end for;

    Mat := Matrix(QQ,[
        [Coefficient(empty[i],v[j],1) : j in [1..dG+1]]
        : i in [1..#empty]
    ]);

    zero := [0 : i in [1..dG+2]];
    V := -Vector(QQ,[Evaluate(empty[i],zero) : i in [1..#empty]]);

    MF := Transpose(Mat);
    ok,y,z := IsConsistent(MF,V);
    assert ok;

    yy := &+[y[i+1]*va^i : i in [0..dG]];
    sigma := bnew-yy*Bnew;

    Sigma := [QQ!Coefficient(sigma,va,0)]
             cat [QQ!Coefficient(sigma,va,i) : i in [1..r-1]];

    return Sigma;
end function;


// ============================================================
// Contribution helpers
// ============================================================

function MakeCon(a,b,c)
    L1 := (a eq 1) select [0,0] else Contribution(a,[b,c]);
    L2 := (b eq 1) select [0,0] else Contribution(b,[a,c]);
    L3 := (c eq 1) select [0,0] else Contribution(c,[a,b]);

    return [
        ((a eq 1) select 0 else L1[(n mod a)+1]-L1[1])
        + ((b eq 1) select 0 else L2[(n mod b)+1]-L2[1])
        + ((c eq 1) select 0 else L3[(n mod c)+1]-L3[1])
        : n in [0..a*b*c-1]
    ];
end function;


function Con(n,a,b,c)
    L1 := (a eq 1) select [0,0] else Contribution(a,[b,c]);
    L2 := (b eq 1) select [0,0] else Contribution(b,[a,c]);
    L3 := (c eq 1) select [0,0] else Contribution(c,[a,b]);

    c1 := L1[(n mod a)+1]-L1[1];
    c2 := L2[(n mod b)+1]-L2[1];
    c3 := L3[(n mod c)+1]-L3[1];

    return c1+c2+c3;
end function;


function LargestElement(vec)
    maxElement := vec[1];

    for i in [2..#vec] do
        if vec[i] ge maxElement then
            maxElement := vec[i];
        end if;
    end for;

    return maxElement;
end function;


// ============================================================
// Exact multiplicity
//
// k = floor(N/sqrt(abc)) + 1
//
// Since
//
// floor(N/sqrt(pro))
//   = Isqrt(floor(N^2/pro)),
//
// this computes k using integer arithmetic only.
// ============================================================

function ExactK(N,pro)
    return Isqrt((N^2) div pro)+1;
end function;


// ============================================================
// Rigorous finite search bound
//
// Original bound:
//
//   2*pro*C / (sqrt(pro)-sum)
//
// Rationalizing:
//
//   2*pro*C*(sqrt(pro)+sum)/(pro-sum^2).
//
// We replace sqrt(pro) in the numerator by its integer ceiling.
// This gives a rigorous UPPER bound, so no candidate can be lost.
//
// Requires pro > sum^2.
// ============================================================

function SafeSearchBound(pro,sum,C)
    if pro le sum^2 then
        error "This search requires abc > (a+b+c)^2.";
    end if;

    s0 := Isqrt(pro);
    sUpper := (s0^2 eq pro) select s0 else s0+1;

    QQ := Rationals();
    upper := (QQ!(2*pro)*C*QQ!(sUpper+sum))/QQ!(pro-sum^2);

    return Ceiling(upper);
end function;

// ============================================================
// Deficiency-0 search
// ============================================================

function Eff(a,b,c)
    Q := Rationals();
    pro := a*b*c;
    sum := a+b+c;

    if pro le sum^2 then
        error "Eff requires abc > (a+b+c)^2.";
    end if;

    startk := 1;
    startn := 1;
    L := MakeCon(a,b,c);
    maxCon := LargestElement(L);
    MaxN := SafeSearchBound(pro,sum,maxCon);

    if MaxN lt 1 then
        return [startn,startk];
    end if;

    for m in [1..MaxN] do
        k := ExactK(m,pro);
        assert m^2-k^2*pro lt 0;

        hval := Q!1 + ((Q!(m^2+m*sum))/pro - Q!(k^2+k))/2;

        if hval + L[(m mod pro)+1] eq 1 then
            startk := k;
            startn := m;
            break;
        end if;
    end for;

    return [startn,startk];
end function;


// ============================================================
// Candidate generator for deficiency i
// ============================================================

function SEff(a,b,c,i)
    Q := Rationals();
    pro := a*b*c;
    sum := a+b+c;

    if pro le sum^2 then
        error "SEff requires abc > (a+b+c)^2.";
    end if;

    startk := [];
    startn := [];
    L := MakeCon(a,b,c);
    maxCon := LargestElement(L);
    MaxN := SafeSearchBound(pro,sum,i+maxCon);

    if MaxN lt 1 then
        return startk,startn;
    end if;

    for n in [1..MaxN] do
        k := ExactK(n,pro);
        assert n^2-k^2*pro lt 0;

        hval := Q!1 + ((Q!(n^2+n*sum))/(Q!pro) - Q!(k^2+k))/2;

        if hval + L[(n mod pro)+1] eq 1-i then
            Append(~startk,k);
            Append(~startn,n);
        end if;
    end for;

    return startk,startn;
end function;


// ============================================================
// Weighted-degree exponent triples
// ============================================================

function ExponentTriples(N,wa,wb,wc)
    triples := [];

    for aExp in [0..N div wa] do
        rem1 := N-wa*aExp;

        for bExp in [0..rem1 div wb] do
            rem2 := rem1-wb*bExp;

            if rem2 mod wc eq 0 then
                Append(~triples,<aExp,bExp,rem2 div wc>);
            end if;
        end for;
    end for;

    return triples;
end function;


// ============================================================
// Derivative triples
//
// Only derivatives of total order d-1 are required here.
//
// In the supported range:
//
//     abc > (a+b+c)^2,
//
// hence max(a,b,c) < sqrt(abc).
//
// For d = floor(N/sqrt(abc))+1, weighted Euler recursion
// shows that vanishing of all derivatives of order d-1
// forces vanishing of all lower-order derivatives.
// Thus these rows impose multiplicity at least d.
// ============================================================

function RowTriples(d)
    rows := [];

    for u in [0..d-1] do
        for v in [0..d-1-u] do
            w := d-1-u-v;
            Append(~rows,<u,v,w>);
        end for;
    end for;

    return rows;
end function;


// ============================================================
// Modular Hasse-derivative rank test
//
// We omit the factor u!v!w!.
//
// This merely rescales each row over Q, so it does not change
// the Q-kernel or Q-rank. The resulting Hasse-derivative matrix
// has much smaller entries.
//
// Full column rank modulo ANY prime certifies full column rank
// over Q.
// ============================================================

function ModularFullColumnRank(rowTriples,cols,p)
    Fp := GF(p);
    r := #rowTriples;
    n := #cols;
    Xp := ZeroMatrix(Fp,r,n);

    for j in [1..r] do
        u := rowTriples[j][1];
        v := rowTriples[j][2];
        w := rowTriples[j][3];

        for col in [1..n] do
            Aexp := cols[col][1];
            Bexp := cols[col][2];
            Cexp := cols[col][3];

            Xp[j,col] :=
                (Fp!Binomial(Aexp,u))
                * (Fp!Binomial(Bexp,v))
                * (Fp!Binomial(Cexp,w));
        end for;
    end for;

    rk := Rank(Xp);
    return rk eq n,rk;
end function;


// ============================================================
// Exact integer rank of Hasse-derivative matrix
// ============================================================

function ExactMatrixRank(rowTriples,cols)
    r := #rowTriples;
    n := #cols;
    X := ZeroMatrix(Integers(),r,n);

    for j in [1..r] do
        u := rowTriples[j][1];
        v := rowTriples[j][2];
        w := rowTriples[j][3];

        for col in [1..n] do
            Aexp := cols[col][1];
            Bexp := cols[col][2];
            Cexp := cols[col][3];

            X[j,col] :=
                Binomial(Aexp,u)
                * Binomial(Bexp,v)
                * Binomial(Cexp,w);
        end for;
    end for;

    return Rank(X);
end function;


// ============================================================
// Desired curves
// ============================================================
function DesiredCurves(a,b,c,def_i)
   printf "WPS: P%o\n------------------\n",[a,b,c];

   pro := a*b*c; sum := a+b+c;
   if pro le sum^2 then
      error "DesiredCurves requires abc > (a+b+c)^2.";
   end if;

   Pair := Eff(a,b,c);
   if &*Pair ne 1 then
      printf "Output of Eff function: %o\n",Pair;
      printf "================================================= i=%o\n",def_i;
      return false;
   end if;

   M,N := SEff(a,b,c,def_i);
   if #N eq 0 then
      printf "================================================= i=%o\n",def_i;
      return false;
   end if;

   foundAny := false;

   for idx in [1..#N] do
      d := M[idx]; Ndeg := N[idx];
      rowTriples := RowTriples(d);
      cols := ExponentTriples(Ndeg,a,b,c);
      r := #rowTriples; n := #cols;

      if n eq 0 then
         continue;
      end if;

      // More columns than equations => nonzero kernel automatically.
      if n gt r then
         printf "Desired Curve may appear for Deficiency: %o, k=%o, n=%o\n",
                def_i,d,Ndeg;
         foundAny := true;
         continue;
      end if;

      // Modular pretest: full column rank modulo one prime
      // certifies zero kernel over Q.
      certifiedNoCurve := false;
      for p in MODULAR_PRIMES do
         fullRank,rk := ModularFullColumnRank(rowTriples,cols,p);
         if fullRank then
            certifiedNoCurve := true;
            break;
         end if;
      end for;

      if certifiedNoCurve then
         continue;
      end if;

      // Only inconclusive modular cases reach exact rank.
      exactRank := ExactMatrixRank(rowTriples,cols);
      if n-exactRank ge 1 then
         printf "Desired Curve may appear for Deficiency: %o, k=%o, n=%o\n",
                def_i,d,Ndeg;
         foundAny := true;
      end if;
   end for;

   printf "================================================= i=%o\n",def_i;
   return foundAny;
end function;
// ============================================================
// Helper to run a list of WPS cases
// ============================================================

function RunCases(L,def_i)
    Found := [];

    for I in L do
        a,b,c := Explode(I);

        if DesiredCurves(a,b,c,def_i) then
            Append(~Found,I);
        end if;
    end for;

    return Found;
end function;


// ============================================================
// Previously skipped cases
// ============================================================

L1 := [
    [5,37,61],
    [5,41,68],
    [9,13,55]
];

L2 := [
    [5,33,49],
    [5,37,61],
    [5,41,68],
    [5,48,79],
    [5,56,83],
    [5,56,93],
    [5,59,97],
    [7,11,20],
    [7,13,16],
    [7,13,24],
    [7,24,85],
    [9,13,55],
    [9,16,67],
    [9,17,74],
    [9,22,91],
    [10,13,61]
];

L3 := [
    [5,33,49],
    [5,37,61],
    [5,41,68],
    [5,48,79],
    [5,56,83],
    [5,56,93],
    [5,59,97],
    [7,11,20],
    [7,13,16],
    [7,13,23],
    [7,13,24],
    [7,15,19],
    [7,16,17],
    [7,16,29],
    [7,16,31],
    [7,17,33],
    [7,19,34],
    [7,20,37],
    [7,24,85],
    [8,15,43],
    [9,10,13],
    [9,10,23],
    [9,11,28],
    [9,13,55],
    [9,16,67],
    [9,17,74],
    [9,19,79],
    [9,22,91],
    [9,23,98],
    [10,13,61],
    [10,17,79],
    [10,19,93],
    [10,21,97]
];

KnownDef1 := [
    [8,15,43],
    [5,33,49],
    [13,15,68],
    [5,56,83]
];


// ============================================================
// Deficiency 1
// ============================================================

print "\n############################################################";
print "DEFICIENCY 1";
print "############################################################";

FoundDef1New := RunCases(L1,1);

printf
    "\nNew deficiency-1 cases among previously skipped cases:\n%o\n",
    FoundDef1New;


// ============================================================
// Deficiency 2
// ============================================================

L2run := [
    I : I in L2 |
    not (I in KnownDef1) and
    not (I in FoundDef1New)
];

printf "\nDeficiency-2 cases to run: %o\n",#L2run;
printf "%o\n",L2run;

print "\n############################################################";
print "DEFICIENCY 2";
print "############################################################";

FoundDef2 := RunCases(L2run,2);

printf "\nDeficiency-2 cases found:\n%o\n",FoundDef2;


// ============================================================
// Deficiency 3
// ============================================================

L3run := [
    I : I in L3 |
    not (I in KnownDef1) and
    not (I in FoundDef1New) and
    not (I in FoundDef2)
];

printf "\nDeficiency-3 cases to run: %o\n",#L3run;
printf "%o\n",L3run;

print "\n############################################################";
print "DEFICIENCY 3";
print "############################################################";

FoundDef3 := RunCases(L3run,3);


// ============================================================
// Final summary
// ============================================================

print "\n############################################################";
print "FINAL SUMMARY";
print "############################################################";

printf
    "\nPreviously known deficiency-1 cases:\n%o\n",
    KnownDef1;

printf
    "\nAdditional deficiency-1 cases among skipped computations:\n%o\n",
    FoundDef1New;

printf
    "\nDeficiency-2 cases found:\n%o\n",
    FoundDef2;

printf
    "\nDeficiency-3 cases found:\n%o\n",
    FoundDef3;

print "\n############################################################";
print "END";
print "############################################################";


