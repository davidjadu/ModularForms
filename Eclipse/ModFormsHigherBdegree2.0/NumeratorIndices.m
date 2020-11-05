(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["NumeratorIndices`", { "Denominator`","ModularRing`","LieART`","RootsHandling`"}]
(* Exported symbols added here with SymbolName::usage *)  
NumIndex::usage="Numerator Index"
NumWeight::usage="Numerator Weight"
NumGenusIndex::usage="Numerator Index in the string constant"
NumeratorAnsatz::usage="NumeratorAnsatz[algebra,k,nb] gives the ansatz for the numerator in terms of Jacobi forms"
NumTerms::usage="Number of terms in the numerator"
getAnsatz::usage="Gives ansatz for expansion"
Ax;
Bx;
e6;
e4;
\[Phi];
Begin["`Private`"] (* Begin Private Context *) 

NumIndex[algebra_, k_, n_] := -n k + denIndex[algebra, k]

NumWeight[algebra_, k_,n_] := denWeight[algebra, k,n]

NumGenusIndex[algebra_,k_,n_]:= dengsIndex[algebra,k,n]-1/2(n k^2+(2-n)k)

gen[algebra_] := 1/(1 - e4 z^4) 1/(1 - e6 z^6) Product[1/(1 - \[Phi][w[algebra][[i]], d[algebra][[i]]] x^(d[algebra][[i]]) z^-w[algebra][[i]]), {i, 1, LieART`Rank[algebra] + 1}] 1/(1 - Ax y z^(-2))1/(1 - Bx y);

NumeratorAnsatz[algebra_,k_,n_]:=Flatten[{Replace[(SeriesCoefficient[gen[algebra], {x, 0, NumIndex[algebra,k,n]}, {y, 0, NumGenusIndex[algebra,k,n]}, {z, 0, NumWeight[algebra,k,n]}] // 
      Expand), HoldPattern[Plus[x__]] :> List[x]]}];

NumTerms[algebra_,k_,n_]:=Length[NumeratorAnsatz[algebra,k,n]]

getAnsatz[algebra_,weight_,index_,gindex_]:=Flatten[{Replace[(SeriesCoefficient[gen[algebra], {x, 0,index}, {y, 0,gindex}, {z, 0, weight}] // 

      Expand), HoldPattern[Plus[x__]] :> List[x]]}];

End[] (* End Private Context *)

EndPackage[]



