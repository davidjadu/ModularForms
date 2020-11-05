(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["Denominator`", { "RootsHandling`","LieART`","ModularRing`","WeylInvariantPolynomials`"}]
(* Exported symbols added here with SymbolName::usage *)  

denIndex::usage="Denominator Index"
denWeight::usage="Denominator Weight"
De::usage="Den[Algebra,Base Degree] gives the denominator"
dengsIndex::usage="Index in the string coupling"

x::usage="sin[gs/2]^2, x^g-1 si what appears besides the genus g stuff" 

abPairs::usage="Pairs of coef for denominator"
kshort::usage="Effective level for short roots. By default, for simply laced, all roots are LONG"

Begin["`Private`"] (* Begin Private Context *) 

Recast[f_, u_] := Module[{rep, new, d, c, hold},
  rep = y -> -(u^(1/2) - 1/u^(1/2))^2;
  new = 0;
  hold = f;
  d = Exponent[f, u];
  For[d, d >=  0, d--,
   c = (-1)^d Coefficient[hold, u, d];
   new = new + c y^d;
   hold = hold - c y^d /. rep // Simplify;];
  If[hold == 0, new]]

removeHigherOrder = (q_^n_ /; n > M :> 0 );

QQ[algebra_] := Array[Q, Rank[algebra]];

abPairs[k_] := Solve[a b <= k && a > 0 && b > 0, {a, b}, Integers]

diagonalPairs[k_] := Select[abPairs[k], a == b /. # &]

upperDiagonalPairs[k_] := Select[abPairs[k], a > b /. # &]

denContributionNoRoot[m_] := 
 denContributionNoRoot[m] = 
  Recast[Normal[\[Alpha]2[Y^m j] \[Alpha]2[Y^-m j]], Y] /. 
    removeHigherOrder /. y -> x

denContribution[algebra_, m_, root__] := 
 denContributionNoRoot[m] /. (j -> (Times @@ (QQ[algebra]^root)))

c[algebra_?(AlgebraClass[#] == B || AlgebraClass[#] == C || AlgebraClass[#] == F4 &)] := 2
c[G2] := 3
c[algebra_] := 1

DGLong[algebra_, k_] := Module[{ZZ},ZZ=Array[Z[algebra,#]&,Rank[algebra]];
 Expand[(Expand /@ (Times @@ (-\[Alpha]2[(Times @@ (ZZ^(
              ##)))] & /@ (LongRoots[algebra]))))^
   Length[diagonalPairs[k]] Product[
    Times @@ (denContribution[algebra, 
         a - b /. upperDiagonalPairs[k][[i]], #] & /@ LongRoots[algebra]), {i,
      Length[upperDiagonalPairs[k]]}]]/.ZtoTbasis//PowerExpand
	]

kshort[algebra_, k_] :=Floor[k/c[algebra]]

DGShort[algebra_, k_] := Module[{ZZ},ZZ=Array[Z[algebra,#]&,Rank[algebra]];
 Expand[(Expand /@ (Times @@ (-\[Alpha]2[(Times @@ (ZZ^(
              ##)))] & /@ (ShortRoots[algebra]))))^
   Length[diagonalPairs[kshort[algebra, k]]] Product[
    Times @@ (denContribution[algebra, 
         a - b /. upperDiagonalPairs[kshort[algebra, k]][[i]], #] & /@ 
       LongRoots[algebra]), {i, 
     Length[upperDiagonalPairs[kshort[algebra, k]]]}]]/.ZtoTbasis//PowerExpand
]

Dgen[k_] := 
  Expand[Product[Recast[Normal[-\[Alpha]2[Y^m]], Y] /. y -> x, {m, 1, k}]] /. 
   removeHigherOrder;

De[algebra_, k_,n_] := De[algebra,k,n]=
 Series[(\[Eta]^(12)q^(-1/2))^(k Abs[(n-2)]) Dgen[k] DGShort[algebra, k] DGLong[algebra, k], {q, 0, M}]
(* I would have to do something better for the DGShort, in this way in includes al the roots twice for the simply laced groups*)

j[Algebra[B][n_]]:=1/(2n-1)
j[Algebra[C][n_]]:=(n-1)/(n+1)
j[Algebra[A][_]]:=0
j[Algebra[D][_]]:=0
j[G2]:=1/4
j[F4]:=1/3

(*this j in computed for the program below*) 

Computej[a_] := Module[{short, long, res},
  short = (Total /@ (Times[##, 
           Array[x, Rank[a]]] & /@ (ShortRoots[a].Reverse[
            FOrthogonalSimpleCoroots[a]])))^2 // Total;
  long = (Total /@ (Times[##, 
           Array[x, Rank[a]]] & /@ (LongRoots[a].Reverse[
            FOrthogonalSimpleCoroots[a]])))^2 // Total;
  If[NumberQ[res = short/(short + long) // Simplify], res, $Failed]
  ]


h[Algebra[B][n_]]:=(2n-1)
h[Algebra[A][n_]]:=n+1
h[Algebra[C][n_]]:=n+1
h[Algebra[D][n_]]:=2n-2
h[G2]:=4
h[F4]:=9

denIndex[algebra_, k_] := 2 h[algebra] ((1-j[algebra]) Length[abPairs[k]] + j[algebra]Length[abPairs[kshort[algebra, k]]])

denWeight[algebra_, k_,n_] := 6k Abs[(n-2)]- 2k - 2 Length[abPairs[k]] Length[LongRoots[algebra]] -2 Length[abPairs[kshort[algebra,k]]] Length[ShortRoots[algebra]] 
  
dengsIndex[algebra_,k_,nb_]:=k(k+1)(2k+1)/6+ (*This is the contribution from the pure gstnig term, it is the sum of squares up to k*)
 Sum[(a-b)^2/. abPairs[k][[i]],{i,1,Length[abPairs[k]]}] Length[LongRoots[algebra]]+ (*Contribution from the long roots*)
Sum[(a-b)^2/. abPairs[kshort[algebra,k]][[i]],{i,1,Length[abPairs[kshort[algebra,k]]]}] Length[ShortRoots[algebra]] (*Contribution from the short roots*)

End[] (* End Private Context *)

EndPackage[]
