(* Wolfram Language Package *)

(*This package is mainly to rewrite the roots from LieART to a vector form, as by default they are written as text.
 All the F--- represent the exact same thing as in LieART but in vector form*)

BeginPackage["RootsHandling`", { "LieART`"}]
(* Exported symbols added here with SymbolName::usage *)  

dual::usage= "Dual Lie Algebra of a Lie Algebra"
LongRoots::usage ="Long Roots of the given algebra as a list in the root basis"
ShortRoots::usage ="Short Roots of the given algebra as a list in the root basis"
FHighestRoot::usage="Highest Root of the given Lie Algebra in the roots basis"

FOrthogonalSimpleCoroots::usage="Orthogonal Simple Coroots"
FOrthogonalFundamentalCoweights::usage="Orthogonal Fundamental coweights" 

OrthogonalDimension::usage="orth. dim. of the lattices"

Begin["`Private`"] (* Begin Private Context *) 

dual[Algebra[B][n_]] := Algebra[C][n]
dual[Algebra[C][n_]] := Algebra[B][n]

dual[a_] := a (*It is difficult to test if it is an algebra because the \
exeptional lie algebras are saved as atomic Symbols*)

FPositiveCoroots[
  a_] := ((Table[#[[i]], {i, Rank[a]}]) & /@ (PositiveRoots[dual[a]] // 
     AlphaBasis))

OrthogonalDimension[a_] := 
 Switch[AlgebraClass[a], G2, 3, A, Rank[a] + 1, E6, 8, E7, 8, _, Rank[a]]

killing[B3, a__, b__] := a.b
kinv[B3, a__, b__] := 2 a.b

killing[C3, a__, b__] := 2 a.b
kinv[C3, a__, b__] := a.b
killing[_, a__, b__] := a.b
kinv[_, a__, b__] := a.b

FOrthogonalSimpleRoots[a_]:=List @@@ OrthogonalSimpleRoots[a]

FOrthogonalRoots[a_]:=FPositiveRoots[a].FOrthogonalSimpleRoots[a]

(*Note the reversing is due to the different basis chosen*)
FOrthogonalFundamentalCoweights[
  a_] := Switch[a, 
	G2,Reverse[List@@# &/@OrthogonalFundamentalWeights[a]],
	F4,Reverse[List@@# &/@OrthogonalFundamentalWeights[a]],
	_,List@@# &/@OrthogonalFundamentalWeights[dual[a]]
	]

FPositiveRoots[a_] := List @@ # & /@ AlphaBasis[PositiveRoots[a]]

LongRoots[a_] :=LongRoots[a]= Module[{max, norms},
  norms =#.#&/@FOrthogonalRoots[a];
  max = Max[norms]; (*This is the minimal root length, 
  which depends on the conventions in the LieART package, 
  however the exponents in the denominator do not, so this doesn't matter.*)
  FPositiveRoots[a][[#]] & /@ Flatten[Position[norms, max]]
  ]

ShortRoots[a_] := ShortRoots[a]=
  Select[FPositiveRoots[a], (! MemberQ[LongRoots[a], ##]) &]

FHighestRoot[a_] :=List@@AlphaBasis[HighestRoot[a]]

(*Note the reversing is due to the different basis chosen*)

End[] (* End Private Context *)

EndPackage[]