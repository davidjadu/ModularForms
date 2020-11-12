(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["DenominatorBaseDeg1`", {"Denominator`","RootsHandling`","LieART`","ModularRing`","WeylInvariantPolynomials`"}]
(* Exported symbols added here with SymbolName::usage *)  

De1::usage="Den[Algebra,Base Degree] gives the denominator"

Begin["`Private`"] (* Begin Private Context *) 


removeHigherOrder = (q_^n_ /; n > M :> 0 );

QQ[algebra_] := Array[Q, Rank[algebra]];

\[Alpha]2[Z_,max_]:=\[Alpha]2[Z,max]=Series[\[Alpha]2[Z],{q,0,max}];

DG[algebra_,max_] := Module[{ZZ},
	ZZ=Array[Z[algebra,#]&,Rank[algebra]];
 	Expand[(Expand /@ (Times @@ (-\[Alpha]2[(Times @@ (ZZ^(##))),max] & /@ (LongRoots[algebra]))))]
]

De1[algebra_,max_] := (*De1[algebra,max]=*)
 Series[(\[Eta]^(12)q^(-1/2))^(k Abs[(n-2)])DG[algebra, max], {q, 0, max}]

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
