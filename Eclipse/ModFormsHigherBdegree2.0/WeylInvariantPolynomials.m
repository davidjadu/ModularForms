(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["WeylInvariantPolynomials`", { "ModularRing`", "LieART`","RootsHandling`"}]
(* Exported symbols added here with SymbolName::usage *)  

M;

FindInvariants::usage="FindInvariants[algebra] computes the Weyl invariant polynomials and saves them as zInv[algebra,i]"
zInv::usage="Weyl invariants Polynomials. Should be called as zInv[algebra,i]"
SolveInWeylInvariants::usage="SolveInWeylInvariants[algebra,toexpand,index,Max] expands the function the modular function to expand
of index index in terms of the Weyl invariant polynomials of the algebra algebra. It goes as deep as order q^Max, the default value
of Max is M"
ExpandInJacobiForms::usage="ExpandInJacobiForms[algebra,toexpand,index,weight,max] gives the expansion of the function to expand
of index index and index weight in terms of the jacobi forms of algebra. It goes as deep as q^max, the default value of max is M"
\[Phi]exp::usage="phiexp[weight,algebra] gives the jacobi forms in terms of weyl invariant polynomials."

Z::usage="Variable for the polynomials in the coweights basis."
expo::usage="Gives the exponent that makes all powers integers, t^expo=Z"
t::usage="t^expo =Z is the variable in which all the exponents are positive"
tInv::usage="Weyl invariant polynomials in the t-variables"

Pol::usage="General polynomial for the given values"
PolyToWeyl::usage="Polynomial written in Weyl invariant pol"
PolyToWeylIncomplete::usage="The same as PolyToWeyl but works with incomplete data, it stops if the bound is reach"

XtoZbasis::usage="It takes from the orthogonal to the coweights basis" 
ZtoTbasis::usage="Basis change"
XtoTbasis::usage="Basis change"
ZtoXbasis::usage="Basis change"

(*
Tregulator::usage="regulator for the weyl invariant poly"
RegTinv::usage="Regulated weyl invariant polynomial (in t-variable)" *)



\[Phi]weyl::usage="The forms in Weyl inv. polynomials"

p::usage="Variable for Weyl invariant polynomaials"

Begin["`Private`"] (* Begin Private Context *) 

Pol[label_, n_, rk_] := 
 Total[(a[label, #]) (Times @@ (Array[p, rk + 1, {0, rk}]^#)) & /@ 
   Flatten[Permutations /@ (Join[#, Table[0, rk + 1 - Length[#]]] & /@
        IntegerPartitions[n, rk + 1]), 1]]
  

XtoZbasis[algebra_] := Module[{ZZ, XX}, ZZ = Array[Z[algebra, #] &, Rank[algebra]];
 XX = Array[X, Rank[algebra]];
 Thread[XX->(Times @@ # & /@ (ZZ^# & /@ Transpose[FOrthogonalFundamentalCoweights[algebra][[All,1;;Rank[algebra]]]]))]
 ]
             
ZtoTbasis:=(Z[algebra_,i_]:>t[algebra,i]^expo[algebra])

ZtoXbasis[algebra_]:=Solve[X[#]==(X[#]/.XtoZbasis[algebra])&/@Range[Rank[algebra]],Array[Z[algebra,#]&, Rank[algebra]]][[1]];

XtoTbasis[algebra_]:=XtoZbasis[algebra]/.ZtoTbasis//PowerExpand

zInv[algebra_,i_]:=zInv[algebra,i]=Module[{orbit},
	orbit=List @@ # & /@ AlphaBasis[Orbit[Weight[AlgebraClass[algebra]] @@ Table[KroneckerDelta[i, j], {j, Rank[algebra]}]]]; (*Alpha Basis is equivalent to coweight basis*)
	Total[Times @@ # & /@ (Array[Z[algebra,#]&, Rank[algebra]]^# & /@ orbit)]
]

(*Tregulator[algebra_] := 
 Map[Max, Transpose[
   Exponent[tInv[algebra, #], 
      Array[1/t[algebra, #] &, Rank[algebra]]] & /@ 
    Range[Rank[algebra]]]]
    
RegTinv[algebra_,i_]:=(Times @@ (Array[t[algebra, #] &, Rank[algebra]]^Tregulator[algebra])) tInv[algebra, i] // Expand*)

expo[algebra_]:=expo[algebra]=Max[Denominator /@ Flatten[Exponent[#, Array[Z[algebra, #] &, Rank[algebra]]] & /@ (List @@ (zInv[algebra, #] & /@  Range[Rank[algebra]]))]];

tInv[algebra_,i_]:=tInv[algebra]=zInv[algebra,i]/.Z[labels___]:>t[labels]^expo[algebra]//PowerExpand
  
SolveInWeylInvariants[algebra_, toexpand_, Max_:M] := Module[
  {qorder, expan,sol},
  For[qorder = 0, qorder <= Max, qorder++,
   expan[qorder] = PowerExpand[(D[Normal[toexpand], {q, qorder}] /. q -> 0)/
     qorder!/.XtoTbasis[algebra]];
   sol[qorder] =PolyToWeyl[algebra,expan[qorder]]
   ];
  Sum[sol[qorder] q^qorder, {qorder, 0, 
     Max}]]

PolyToWeylIncomplete[algebra_, poly_,bound_] := 
 Module[{moniToVector, vectorToMonis, allEntriesPositiveOrZero, ZZ, 
   pReplacement, polyRed, decompList, i, polyToMonis, monisToVectors, 
   posPosEs, posXVs, posXs, sumsList, maxSumsList, posT, monomInGens, 
   seedsListT, decompositions, linGenListVectors, linGenListMonis, stop,
   coeff}, 
   moniToVector[x_] := Exponent[x, t[algebra, #]^-1] & /@ Range[Rank[algebra]];
  vectorToMonis[x_] := Product[p[i]^x[[i]], {i, 1, Rank[algebra]}];
  allEntriesPositiveOrZero[list_] := And @@ (# >= 0 & /@ list);
  ZZ = Array[Z[algebra, #] &, Rank[algebra]];
  seedsListT = (Exponent[
        Coefficient[#, \[Epsilon]^Exponent[#, \[Epsilon]]] &@(tInv[
            algebra, #] /. t[name__] :> \[Epsilon]^-1 t[name]), 
        Array[t[algebra, #]^ -1 &, Rank[algebra]]]) & /@ Range[Rank[algebra]] // 
    Transpose (* 
  This are (minus) the most negative exponents that appear in tInv*);
  pReplacement = p[#] -> tInv[algebra, #] & /@ Range[Rank[algebra]];
  polyRed = poly;
  decompList = {};
  stop = False;
  While[!stop&&!NumberQ[polyRed],
   polyToMonis = {List @@ Expand[polyRed]}//Flatten;
   monisToVectors = moniToVector[#] & /@ polyToMonis;
   decompositions = LinearSolve[seedsListT, #] & /@ monisToVectors;
   linGenListVectors = 
    Select[decompositions, allEntriesPositiveOrZero[#] &];
   linGenListMonis = vectorToMonis[#] & /@ linGenListVectors;
   posPosEs = 
    Flatten[Position[decompositions, #] & /@ linGenListVectors];
   posXVs = monisToVectors[[#]] & /@ posPosEs;
   posXs = polyToMonis[[#]] & /@ posPosEs;
   sumsList = Plus @@@ (Abs[#] & /@ posXVs);
   maxSumsList = Max[Plus @@@ sumsList];
   If[maxSumsList<bound,stop=True]; (*To ensure we don't go farther that we can with the info we have*)
   posT = Flatten[Position[sumsList, maxSumsList]][[1]];
   coeff = posXs[[posT]] /. t[__] -> 1;
   monomInGens = coeff linGenListMonis[[posT]];
   decompList = Join[decompList, {monomInGens}];
   polyRed =1+(Expand[# - Coefficient[#, \[Epsilon], 0] - \[Epsilon] Coefficient[#, \[Epsilon], 1]]&@
    Expand[polyRed - monomInGens /. pReplacement/.(t[__]^n_ /; n > 0:> 0)/.t[name__]:>\[Epsilon] t[name]]
   	/.(\[Epsilon]^n_ /; n >-bound:> 0))/.\[Epsilon]->1;(*This removes everything beyond the bound*)
  ];

  
  decompList=Join[decompList,{polyRed-1}];
  Plus @@ decompList]
  
PolyToWeyl[algebra_, poly_] :=
 Module[{moniToVector, vectorToMonis, allEntriesPositiveOrZero, ZZ, 
   pReplacement, polyRed, decompList, i, polyToMonis, monisToVectors, posPosEs, posXVs, posXs, sumsList, 
   maxSumsList, posT, monomInGens, seedsListT, decompositions, 
   linGenListVectors, linGenListMonis, coeff},
  moniToVector[x_] := 
   Exponent[x, t[algebra, #]] & /@ Range[Rank[algebra]];
  vectorToMonis[x_] := Product[p[i]^x[[i]], {i, 1, Rank[algebra]}];
  allEntriesPositiveOrZero[list_] := And @@ (# >= 0 & /@ list);
  ZZ = Array[Z[algebra, #] &, Rank[algebra]];
  seedsListT = 
   expo[algebra] (LinearSolve[
         List @@@ OrthogonalSimpleRoots[algebra] // 
          Transpose, #] & /@ (List @@@ 
         OrthogonalFundamentalWeights[algebra])) // Transpose;
  pReplacement = p[#] -> tInv[algebra, #] & /@ Range[Rank[algebra]];
  polyRed = poly;
  decompList = {};
  While[! NumberQ[polyRed],
   polyToMonis = List @@ Expand[polyRed];
   monisToVectors = moniToVector[#] & /@ polyToMonis;
   decompositions = LinearSolve[seedsListT, #] & /@ monisToVectors;
   linGenListVectors = 
    Select[decompositions, allEntriesPositiveOrZero[#] &];
   linGenListMonis = vectorToMonis[#] & /@ linGenListVectors;
   posPosEs = 
    Flatten[Position[decompositions, #] & /@ linGenListVectors];
   posXVs = monisToVectors[[#]] & /@ posPosEs;
   posXs = polyToMonis[[#]] & /@ posPosEs;
   sumsList = Plus @@@ (Abs[#] & /@ posXVs);
   maxSumsList = Max[Plus @@@ sumsList];
   posT = Flatten[Position[sumsList, maxSumsList]][[1]];
   coeff = posXs[[posT]] /. t[__] -> 1;
   monomInGens = coeff linGenListMonis[[posT]];
   decompList = Join[decompList, {monomInGens}];
   polyRed = Expand[polyRed - monomInGens /. pReplacement]];
  decompList = Join[decompList, {polyRed}];
  Plus @@ decompList]  

\[Phi]weyl[i__, algebra_, max_ : M] := \[Phi]weyl[i, algebra,max] = 
  SolveInWeylInvariants[algebra, \[Phi][i, algebra], max]


(* ::Subsubsection:: *)
(* Region Title *)


ExpandInJacobiForms[algebra_, toexpand_, index_, weight_, max_:M] := 
 Module[{gen, Ansatz, difference, variables, solution, i, terms, 
   numTerms},
  gen = 1/(1 - e4 z^4) 1/(1 - e6 z^6)Product[
     1/(1 - \[Phi][wlabel[algebra][[i]], d[algebra][[i]], 
          algebra] x^(d[algebra][[i]]) z^-w[algebra][[i]]), {i, 1, 
      Rank[algebra] + 1}];
    terms = 
   Flatten[{Replace[(SeriesCoefficient[
         gen, {x, 0, index}, {z, 0, weight}] // Expand), 
      HoldPattern[Plus[x__]] :> List[x]]}]; 
      
      	numTerms = Length[terms];
	
	Print["The number of terms to solve is ",numTerms];
      
   (* Print[terms];*)
      
  Monitor[Ansatz = 
   Sum[c[i] Expand[##[[i]] /. {\[Phi][a_, b_, algebra] :> \[Phi]weyl[
              a, algebra, max], e4 -> Normal[Ei4], 
            e6 -> Normal[Ei6]} /. p[0] -> 1 /. 
         q^n_ /; n > max :> 0], {i, Length[##]}] &@terms, i];

	(*Print[Ansatz];*)


	difference = toexpand - Ansatz;

(*Return[difference];*)

  variables = Array[p, #] &@Rank[algebra];
  solution[-1] = {};
  solution[j_] := solution[j] = Join[solution[j - 1] /. #, #] &@
     Solve[
       CoefficientRules[
       (*	Coefficient[q difference//Expand,q^(i+1)]/.solution[i-1]*)
          Expand[PowerExpand[
             D[difference, {q, i}] /. q -> 0 /. solution[i - 1]]],variables][[All, 2]] == 
        0][[1]];
  i = 0;
  Print[StringJoin["So far, I have solved for ", 
    ToString[Length[Select[solution[i-1],MatchQ[c[__]->__]]]], " of ", ToString[numTerms], 
    " terms." , " I am checking the solution at order q ^" , 
    ToString[i], " just a sec ..."]];
  While[Length[Select[solution[i],MatchQ[c[__]->__]]] < numTerms && i < max, i++; 
   Print[StringJoin["So far, I have solved for ", 
     ToString[Length[Select[solution[i-1],MatchQ[c[__]->__]]]], " of ", ToString[numTerms], 
     " terms." , " I am checking the solution at order q ^" , 
     ToString[i], " just a sec ..."]];
     ];
  Print["I managed to solve for ",ToString[Length[Select[solution[i],MatchQ[c[__]->__]]]]," of ", ToString[numTerms]," terms at order q ^", 
     ToString[i]]; 
  Sum[c[i] ##[[i]],{i,1,Length[##]}] &@terms /. solution[i]
  ]
  
End[] (* End Private Context *)

EndPackage[]
