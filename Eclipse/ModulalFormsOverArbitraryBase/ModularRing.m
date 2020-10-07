(* Wolfram Language Package *)

BeginPackage["ModularRing`",{"LieART`"}]
(* Exported symbols added here with SymbolName::usage *)  

M=3
q;
Z;

$Assumptions=$Assumptions&&X[var_]>0;

\[Eta]::usage="Dedekind eta function"
\[Theta]1::usage="Theta_1 form"
\[Theta]2::usage="Theta_1 form"
\[Theta]3::usage="Theta_1 form"
\[Theta]4::usage="Theta_1 form"

Ei2::usage="Eisenstein Series E2"
Ei4::usage="Eisenstein Series E4"
Ei6::usage="Eisenstein Series E6"

\[Alpha]::usage = "i theta_1/eta^3, the half integer index modular form"
\[Alpha]2::usage = "alpha^2"

\[Phi]::usage="All modular forms are obtained as phi[index, algebra], all the forms are saved once run"
e4::usage="Holder for Eisenstein series"
e6::usage="Holder for Eisenstein series"

d::usage="d[algebra] are the indices of the basis of Jacobi forms"
w::usage="w[algebra] are the weights of the basis of Jacobi forms"
wlabel::usage="labels for the jacobi forms, for most of them we use the weights, there is a porblem for D4, where there is more than 1 weight"

Begin["`Private`"] (* Begin Private Context *) 


d[B3] = {1, 1, 1, 2};
w[B3] = {0, 2, 4, 6};
d[B4] = {1, 1, 1, 1,1};
w[B4] = {0, 2, 4, 6,8};
d[C3] = {1, 1, 1, 1};
w[C3] = {0, 2, 4, 6};

d[C4] = {1, 1, 1, 1,2};
w[C4] = {0, 2, 4, 6,8};

d[F4] = {1, 1, 2, 2,3};
w[F4] = {0, 2, 6, 8,12};

d[D5]={1,1,1,1,2,2};
w[D5]={0,2,4,5,6,8};
wlabel[D5]={0,2,4,{5,1},6,8}

d[D4] ={1,1,1,1,2};
w[D4] = {0,2,4,4,6};
wlabel[D4] = {0,2,4,{4,1},6};
wlabel[algebra_]:=w[algebra]



d[A1] = {1, 1};
w[A1] = {0, 2};

d[A2] = {1, 1, 1};
w[A2] = {0, 2, 3};
d[G2] = {1, 1, 2};
w[G2] = {0, 2, 6};



(* ::Section:: *)
(* Dedekind and Jacobi theta functions*)

\[Eta] := \[Eta] = Series[q^(1/24) Product[(1 - q^n), {n, 1, M}], {q, 0, M + 1}];

\[CapitalTheta][a_, b_, Z_] := 
 Series[Sum[
   Exp[2 \[Pi] I b n] Z^(n + a) q^(1/2 (n + a)^2), {n, -Ceiling[Sqrt[M] + 1], 
    Ceiling[Sqrt[M] + 1]}], {q, 0, M + 1}](*Z=Exp[2i\[Pi]z]*)

\[Theta]1[Z_] :=\[Theta]1[Z] = I \[CapitalTheta][1/2, 1/2, Z];
\[Theta]2[Z_] :=\[Theta]2[Z] =\[CapitalTheta][1/2, 0, Z];
\[Theta]3[Z_] :=\[Theta]3[Z] =\[CapitalTheta][0, 0, Z];
\[Theta]4[Z_] :=\[Theta]4[Z] =\[CapitalTheta][0, 1/2, Z];

(* ::Section:: *)
(* Eisentein Series*)

Eisenstein[k_] := 
 1 + (2/Zeta[1 - k]) Series[
    Sum[(n^(k - 1) q^n)/(1 - q^n), {n, 1, M}], {q, 0, M}]

Ei2 := Ei2 =Eisenstein[2];
Ei4 := Ei4 = Eisenstein[4];
Ei6 := Ei6 = Eisenstein[6];

(* ::Section:: *)
(* A type modular forms*)

diff[f_, l_] := Sum[X[k] \!\(
\*SubscriptBox[\(\[PartialD]\), \(X[k]\)]f\), {k, 1, l + 1}] - 
  1/12 Sum[Log[X[k]], {k, 1, l + 1}] Ei2 f

rep1[l_] := X[l + 1] -> Product[X[i]^-1, {i, 1, l}]
rep2[l_] := 
 Log[Product[X[i]^-1, {i, 1, l}]] -> -Sum[Log[X[i]], {i, 1, l}]

\[Alpha][Z_] := I \[Theta]1[Z]/\[Eta]^3

\[Alpha]2[Z_] := \[Alpha]2[Z] = Expand /@ (\[Alpha][Z]^2)

\[Phi]u[l_,Algebra[A][k_]]:= \[Phi]u[l,Algebra[A][k]]=If[l==k+1,
  Product[\[Alpha][X[i]], {i, 1,k+1}] // Simplify,Expand /@ diff[\[Phi]u[l + 1,Algebra[A][k]], k]]

\[Phi][l_,Algebra[A][k_]] :=\[Phi][l,Algebra[A][k]]= PowerExpand/@Expand/@(\[Phi]u[l,Algebra[A][k]] /. rep1[k] /. rep2[k]//Simplify)

(* ::Section:: *)
(* G2 *)

\[Phi][6,G2] :=\[Phi][6, G2]= Expand /@ (\[Phi][3, A2]^2 // Simplify)

\[Phi][2, G2] :=\[Phi][2, G2]= \[Phi][2, A2]

\[Phi][0, G2] :=\[Phi][0, G2]= \[Phi][0, A2]

(* ::Section:: *)
(* B3*)

matF := 
 Table[If[i > 0, \[Rho][2 i - 2, Z[j]], 1], {j, 0, 3}, {i, 0, 3}]

matG := 
 Table[If[i > 0, \[Rho][2 i - 2, Z[j]], 1], {j, 1, 3}, {i, 0,2}]

F := Det[matF];
G := Det[matG];

factor[
   0] := (F/G /. Table[\[Rho][2 i - 2, Z[0]] -> 0, {i, 0, 3}]) // 
   Simplify;

factor[k_] := 
 factor[k] = Coefficient[F/G, \[Rho][k - 2, Z[0]]] // Simplify

wptemp[
  V_] := (\[Theta]3[1]^2 \[Theta]2[1]^2)/
    4 \[Theta]4[V]^2/\[Theta]1[V]^2 - 
   1/12 (\[Theta]3[1]^4 + \[Theta]2[1]^4) // Simplify (*Be careful, 
  apparently mathematica confuses p and \[Rho]*)

wp[0, V_] := wp[0, V] = wptemp[V];

wp[k_, V_] := wp[k, V] = V \!\(
\*SubscriptBox[\(\[PartialD]\), \(V\)]\(wp[k - 1, V]\)\) // Simplify

Reg[V_] := ((\[Alpha][V]^2)/((V - 1)^2)) // Simplify 

rep := 
  Flatten[Table[\[Rho][2 i - 2, Z[j]] -> 
     Normal[wp[2 i - 2, X[j]]], {i, 1, 3}, {j, 1, 3}]];

\[Phi][6, C3] :=\[Phi][6, C3]= -Collect[
    Expand[Product[\[Alpha][X[i]]^2, {i, 1, 3}] // Normal], q];
    
\[Phi][4, C3] := \[Phi][4, C3]=(Series[
        Product[(X[i] - 1 )^2, {i, 1, 3}] factor[4] /. rep, {q, 0, 
         M}] // FullSimplify)*Product[Reg[X[i]], {i, 1, 3}] // 
    Normal // Expand;
    
\[Phi][2, C3] :=\[Phi][2, C3]= (Series[
        Product[(X[i] - 1 )^2, {i, 1, 3}] factor[2] /. rep, {q, 0, 
         M}] // FullSimplify)*Product[Reg[X[i]], {i, 1, 3}] // 
    Normal // Expand;
    
\[Phi][0, C3] := \[Phi][0, C3]=(Series[
        Product[(X[i] - 1 )^2, {i, 1, 3}] factor[0] /. rep, {q, 0, 
         M}] // FullSimplify)*Product[Reg[X[i]], {i, 1, 3}] // 
    Normal // Expand;

(* ::Section:: *)
(*C3*)

reply[B3] := X[i_] :> X[i]/(X[1]^(1/2) X[2]^(1/2) X[3]^(1/2));

\[Phi][0, B3] := \[Phi][0, B3]=Collect[\[Phi][0, A3] /. reply[B3] // Normal // Expand,q]

\[Phi][2, B3] :=\[Phi][2, B3] =Collect[\[Phi][2, A3] /. reply[B3] // Normal // Expand,q]

\[Phi][4, B3] :=\[Phi][4, B3]= Collect[\[Phi][4, A3] /. reply[B3] // Normal // Expand,q]

\[Phi][6, B3] :=\[Phi][6, B3]= Collect[\[Phi][3, A3]^2 /. reply[B3] // Normal // Expand,q]

(* ::Section:: *)
(*D4*)

\[Phi][0, D4] := \[Phi][0, D4] = 
  Collect[\[Eta]^-12 (\[Theta]3[
          1]^8 Product[\[Theta]3[X[i]], {i, 1, 4}] - \[Theta]4[
          1]^8 Product[\[Theta]4[X[i]], {i, 1, 4}] - \[Theta]2[
          1]^8 Product[\[Theta]2[X[i]], {i, 1, 4}]) // Normal // 
    Expand, q]
\[Phi][2, D4] := \[Phi][2, D4] = 
  Collect[\[Eta]^-12 ((\[Theta]4[1]^4 - \[Theta]2[
            1]^4) Product[\[Theta]3[X[i]], {i, 1, 
           4}] - (\[Theta]2[1]^4 + \[Theta]3[1]^4) Product[\[Theta]4[
           X[i]], {i, 1, 
           4}] + (\[Theta]3[1]^4 + \[Theta]4[1]^4) Product[\[Theta]2[
           X[i]], {i, 1, 4}]) // Normal // Expand, q]
\[Phi][4, D4] := \[Phi][4, D4] = 
  Collect[\[Eta]^-12 (Product[\[Theta]3[X[i]], {i, 1, 4}] - 
        Product[\[Theta]4[X[i]], {i, 1, 4}] - 
        Product[\[Theta]2[X[i]], {i, 1, 4}]) // Normal // Expand, q]
\[Phi][{4,1}, D4] := \[Phi][{4,1}, D4] = 
  Collect[Product[\[Alpha][X[i]], {i, 1, 4}] // Normal // Expand, q]
  
  wreg[X_]:=(wptemp[X](X-1)^2//Normal//Cancel)+O[q]^(M+1)
  
\[Phi][6, D4] := \[Phi][6, D4] = 
  Collect[Product[Reg[X[i]], {i, 1, 4}] Sum[
       wreg[X[i]]Product[If[i!=j,(X[j]-1)^2,1],{j,1,4}], {i, 1, 4}] //Cancel// Normal // Expand, q]

(* ::Section:: *)
(*F4*)
\[Phi][0, F4]:=\[Phi][0, F4]= Normal[\[Phi][0, D4] - 2/3 Ei4 \[Phi][4, D4]]/. {X[1] -> X[1] X[2], 
  X[2] -> X[3]^-1 X[4]^-1, X[3] -> X[1] X[2]^-1, X[4] -> X[3] X[4]^-1}
  
\[Phi][2, F4]:=\[Phi][2, F4]=\[Phi][2, D4]/. {X[1] -> X[1] X[2], 
  X[2] -> X[3]^-1 X[4]^-1, X[3] -> X[1] X[2]^-1, X[4] -> X[3] X[4]^-1}

\[Phi][6, F4]:=\[Phi][6, F4]=\[Phi][6, D4] - 
  1/18 \[Phi][4, D4] \[Phi][2, D4] /. {X[1] -> X[1] X[2], 
  X[2] -> X[3]^-1 X[4]^-1, X[3] -> X[1] X[2]^-1, X[4] -> X[3] X[4]^-1}
  
\[Phi][8, F4]:=\[Phi][8, F4]=\[Phi][4, D4]^2 + 3 \[Phi][{4, 1}, D4]^2 /. {X[1] -> X[1] X[2], 
  X[2] -> X[3]^-1 X[4]^-1, X[3] -> X[1] X[2]^-1, X[4] -> X[3] X[4]^-1}

\[Phi][12, F4]:=\[Phi][12, F4]=\[Phi][4, D4] \[Phi][{4, 1}, D4]^2 - 1/9 \[Phi][4, D4]^3 /. {X[1] -> X[1] X[2], 
  X[2] -> X[3]^-1 X[4]^-1, X[3] -> X[1] X[2]^-1, X[4] -> X[3] X[4]^-1}
(* ::Section:: *)

(* ::Section:: *)
(*D8*)

\[Phi][{8, 1}, D8] := 
  Collect[Product[\[Alpha][X[i]], {i, 1, 8}] // Normal // Expand, q];
  
\[Phi][4, D8] := 
  1/\[Eta]^24*
    Expand /@ (Ei4*(Product[\[Theta]1[X[i]], {i, 1, 8}] + 
          Product[\[Theta]2[X[i]], {i, 1, 8}] + 
          Product[\[Theta]3[X[i]], {i, 1, 8}] + 
          Product[\[Theta]4[X[i]], {i, 1, 8}]) - (Product[\[Theta]2[
            X[i]], {i, 1, 8}] (\[Theta]2[1])^8 + 
         Product[\[Theta]3[X[i]], {i, 1, 8}] (\[Theta]3[1])^8 + 
         Product[\[Theta]4[X[i]], {i, 1, 8}] (\[Theta]4[1])^8)) - 
   Ei4 \[Phi][{8, 1}, D8]  
   
Hdiff[k_, m_, f_] := (q \!\(
\*SubscriptBox[\(\[PartialD]\), \(q\)]f\) - 1/(2 m) Sum[X[i] \!\(
\*SubscriptBox[\(\[PartialD]\), \(X[i]\)]f\) + X[i]^2 \!\(
\*SubscriptBox[\(\[PartialD]\), \(X[i]\)]\(
\*SubscriptBox[\(\[PartialD]\), \(X[i]\)]f\)\), {i, 1, 8}]) - (
   2 k - 8)/24 Ei2 f

\[Phi][2, D8] := Expand /@ (3 Hdiff[-4, 1, \[Phi][4, D8]])

\[Phi][0, D8] := 
 Expand /@ ((2 Hdiff[-2, 1, \[Phi][2, D8]] - Ei4 \[Phi][4, D8])/32);
 
perm[k_] := 
 perm[k] = 
  DeleteDuplicates[
   Sort /@ FoldPairList[TakeDrop, #, {k, 8 - k}] & /@ 
    Permutations[Array[# &, 8]]]
     
\[Phi][k2_, D8] := \[Phi][k2, D8] = 
  Expand /@ 
   Total[Times @@ # & /@ (Join[(((\[Phi][2, A1] /. 
               X[1] :> X[#]) &) /@ #[[
            1]]), (((\[Phi][0, A1] /. X[1] :> X[#]) &) /@ #[[2]])] & /@
        perm[k2/2])]

(* ::Section:: *)

(* ::Section:: *)
(*D5*)
\[Phi][{5, 1}, D5] := \[Phi][{5, 1}, D5] =
  Collect[Product[\[Alpha][X[i]], {i, 1, 5}] // Normal // Expand, q];
  
\[Phi][k_, D5]:= \[Phi][k, D5] =\[Phi][k, D8]/.{X[8]->1,X[7]->1,X[6]->1}//Normal

(* ::Section:: *)

(* Package Postscript*)




End[] (* End Private Context *)

EndPackage[]