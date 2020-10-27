(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["CoefficientFixing`", { "Special`", "Denominator`", "RootsHandling`", "NumeratorIndices`", "ModularRing`", "LieART`","WeylInvariantPolynomials`"}]
(* Exported symbols added here with SymbolName::usage *)  

solve::usage="das ist good "
getGVInvariants::usage="functions that returns the GV invariants given the num expansion"
JacSol::usage="When using solve, the results are saved in here"

Begin["`Private`"] (* Begin Private Context *) 

(*THis only works for base deg. 1 and the Higgsing three over F3*)

(* This are the smallest (most negative) exponents in the weyl invariants (with positive sign), this helps solving the divergent part easily*)
tInvExpos[algebra_] := 
 Table[SortBy[
    CoefficientRules[
      tInv[algebra, i] /. t[name__] :> 1/nt[name] /. 
       nt[__]^n_ /; n < 0 :> 0, 
      Array[nt[algebra, #] &, Rank[algebra]]][[All, 1]], Total] // 
   Last, {i, 1, Rank[algebra]}]
   
(* THis gives the ansatz for a weyl invariant polynomial so that fact*poly is polynomial in the t var, it is also bounded by the degree*)   

givePoly[algebra_,fact_,degree_,label_]:=Module[{factexpos,aa,sols},
	factexpos=CoefficientRules[fact, Array[t[algebra, #] &, Rank[algebra]]][[All, 1]][[1]];
	aa=Array[a,Rank[algebra]];
	sols=Solve[factexpos>= aa.tInvExpos[algebra] && aa >= 0 && Total[aa]<=degree, aa, Integers];
	Total[k[label,aa]Product[p[i]^a[i],{i,1,Rank[algebra]}]/.sols]
]


(* ::Subsubsection:: *)
(* Region Title *)


Options[solve]={SavingPath->False,FileName-> Null,bound->10,Shift->0,Tshift->False,debugging->False}



(* ::Subsubsection:: *)
(* Region Title *)


solve[algebra_,nbase_ (*, inv_*),M_ : M,OptionsPattern[]] := 
(* solve[algebra, M] =*) 
  Module[{df, qorder, fde, fullfact, 
    NumberofTerms,
    res, Pnumi, Pde, guess, possibilities, invariants, solun, resun, tt,ZZ, tshift,ntnt,nt, \[Epsilon], FullSol,index,jacsol,tbound,extrafactor},
   Print["I am starting"];
   Print[Now];
   Off[Solve::svars]; (*To avoid the error message*)
   tt = Array[t[algebra,#]&, Rank[algebra]];
   ZZ = Array[Z[algebra,#]&,Rank[algebra]];
   ntnt = Array[nt[algebra,#]&, Rank[algebra]];
   fde = (Times @@ (ZZ^(##)) &@Total@LongRoots[algebra])/.ZtoTbasis//PowerExpand;
   If[OptionValue[Tshift]===False,
   	extrafactor=1; tshift=Table[0,Rank[algebra]],
   	extrafactor=Times@@(tt^OptionValue[Tshift]); tshift=OptionValue[Tshift]];
   
   If[OptionValue[debugging],Print[extrafactor, " and ", tshift]];
   
   
   fullfact[qorder2_] := extrafactor*
    fde/(Times @@ (ZZ^(FHighestRoot[algebra])))^((*(nbase-2)*)Max[0,nbase-2]- qorder2)/.ZtoTbasis//PowerExpand;
   df=NumIndex[algebra,1,nbase];
   Print["The degree and weight of the numerator are =",df," and ",NumWeight[algebra,1,nbase]];
   Print["I am starting to solve ",Now];
   
   (* Print[fullfact[0]];*)
   
   FullSol[algebra, -1] = {};
   res[qorder2_] := 
    res[qorder2] =  givePoly[algebra,fullfact[qorder2],df+qorder2,{num,qorder2}] /. p[k_] :> tInv[algebra, k] // Expand;
   NumberofTerms[qorder2_]:=givePoly[algebra,fullfact[qorder2],df+qorder2,{num,qorder2}]//Length;
   
      Print["the number of terms in Weyl pol is ", ToString[NumberofTerms[0]]," and ",ToString[NumberofTerms[1]]];
   
   If[NumberQ[OptionValue[bound]],tbound[_]=OptionValue[bound],tbound[i_]:=OptionValue[bound][[i+1]]];
   
   Pnumi[qorder2_] :=
    Pnumi[qorder2] = 
     Series[Sum[(Q[0])^index res[index]*fullfact[index] /. 
            FullSol[algebra, qorder2 - 1], {index, 0, qorder2}] /. t[name___] :> \[Epsilon] t[name]//Expand, {\[Epsilon], 0, tbound[qorder2]}] // Normal; 
   Pde[qorder2_] := 
    Pde[qorder2] = -Expand /@ 
        Series[Coefficient[
          fde (Series[De[algebra,1,nbase] // Normal, {q, 0, qorder2}] // 
               Normal) /. 
            q -> Q[0] (Times @@ (ZZ^(FHighestRoot[algebra])/.ZtoTbasis)) /. 
           t[name__] -> \[Epsilon] t[name], x], {\[Epsilon], 0, tbound[qorder2]}] // 
      Normal;
   guess[qorder2_] := 
    guess[qorder2] = 
     If[qorder2 != 0, 
      Series[Coefficient[
         Series[Pnumi[qorder2]/Pde[qorder2]/.FullSol[algebra,qorder2-1], {Q[0], 0, qorder2}], Q[0]^
         qorder2], {\[Epsilon], 0, tbound[qorder2]}] // Normal, 
      Series[Pnumi[qorder2]/Pde[qorder2], {\[Epsilon], 0, tbound[qorder2]}] // 
       Normal];
   
	(*With[{qorder2=0},Print[givePoly[algebra,fullfact[qorder2],df+qorder2,{num,qorder2}] ]];
	Print[Pnumi[0]];*)
	
   possibilities[x_] := 
    Flatten[Permutations /@ (Join[
          Table[0, {i, 1, Rank[algebra] - Length[##]}], ##] & /@ 
        IntegerPartitions[x, Rank[algebra]]), 1] ; 
   invariants[baseDeg_, x_] := 
    Total[(Global`GV[algebra, baseDeg+OptionValue[Shift], (##-tshift)/expo[algebra]] (Times @@ (tt^##))) & /@ 
       possibilities[x]] // Expand; 
   solun[_, -1] = {};
    (*   
   
   invClean[qorder2_]:=Select[
  inv, #[[1]][[-1]] == 0 && #[[1]][[-2]] == 1&& #[[1]][[-3]] == qorder2+OptionValue[Shift] && 
   Total[#[[1]][[1 ;; -4]]] < OptionValue[bound]/expo[algebra] &];
   
   Print[OptionValue[Shift]];
   Print[OptionValue[bound]];
   Print[invClean[1]];
   
   numInv[qorder2_]:=Length[invClean[qorder2]];
   
   solun[_,0]={};
   solun[qorder2_,i_]:=Join[solun[qorder2,i-1]/.#,#]&@Solve[Coefficient[Q[0](Times@@(ZZ^Table[1,Rank[algebra]]/.ZtoTbasis))guess[qorder2]/.\[Epsilon]->1, 
  Q[0]^(invClean[qorder2][[i]][[1]][[-3]]+1)*Times @@ (ZZ^(invClean[qorder2][[i]][[1]][[1 ;; -4]]+Table[1,Rank[algebra]])) /. 
   ZtoTbasis] - invClean[qorder2][[i]][[2]]==0][[1]];
   
   Print[solun[0,1]];
   
   *)
   
   resun[qorder2_, n_] := 
    If[n != 0, 
     Coefficient[guess[qorder2] /. solun[qorder2, n - 1], \[Epsilon]^n],
      guess[qorder2] /. \[Epsilon] -> 0];
      
   solun[qorder2_, n_] := 
    solun[qorder2, n] = 
     Join[solun[qorder2, n - 1] /. ##, ##] &@
      Solve[CoefficientRules[(resun[qorder2, n] - invariants[qorder2, n])//Expand,
            tt][[All, 2]] == 0][[1]];     
            
   FullSol[algebra, qorder2_] := 
    Join[FullSol[algebra, qorder2 - 1], solun[qorder2,tbound[qorder2]]];
   
   (*Return[guess[1]];*)
   (*Return[{resun[1,1],invariants[1,1]}];*)
   
   
   Do[
    Print[
     StringJoin["I was able to solve for ", 
      ToString[
       Length[FullSol[algebra, qorder]] - Length[FullSol[algebra, qorder - 1]]], 
       " coefficients, out of ", ToString[NumberofTerms[qorder]], 
       " at order q^", ToString[qorder]]];
       If[OptionValue[debugging],Print[FullSol[algebra,qorder]]];
    Print[Now];
    , {qorder, 0, M}];
    
   On[Solve::svars]; 
   
   Print["Got the solution, will expand in Jacobi Forms"];
   Print[Now];
   
   jacsol=ExpandInJacobiForms[algebra,Sum[q^index  givePoly[algebra,fullfact[index],df+index,{num,index}]/.FullSol[algebra, M], {index, 0, M}],df,NumWeight[algebra,1,nbase],M];
   
   Print["I am Done"];
   Print[Now];
 
   If[OptionValue[SavingPath]===False,_,
   	Print["Saving",Now];
	SetDirectory[OptionValue[SavingPath]];
	Export[OptionValue[FileName], jacsol];
   ];
   
   JacSol[algebra,nbase]=jacsol
   
   ]
   
Options[getGVInvariants]={SavingPath->False,FileName-> Null}
getGVInvariants[algebra_,num_,tmax_,M_:M,OptionsPattern[]]:=Module[{Ztop,numExpansion,denExpansion,fde,fullfact,ZZ,tt,sol},
	ZZ = Array[Z[algebra, #] &, Rank[algebra]];
	tt=Array[t[algebra, #] &, Rank[algebra]];
fde = (Times @@ (ZZ^(##)) &@Total@LongRoots[algebra]) /. ZtoTbasis // 
   PowerExpand;
fullfact = 
  fde/(Times @@ (ZZ^(FHighestRoot[algebra]))) /. ZtoTbasis // 
   PowerExpand;
   Print["Expanding Numerator",Now];
numExpansion = 
  Expand[fullfact Expand[
          num /. {\[Phi][a_, __] :> \[Phi]weyl[a, algebra, M], 
            e4 -> Normal[Ei4], e6 -> Normal[Ei6]}] /. 
        q^n_ /; n > M :> 0 /. 
       q -> Q[0] (Times @@ (ZZ^(FHighestRoot[algebra]) /. 
             ZtoTbasis)) /. p[i_] :> tInv[algebra, i]] /. 
    t[name__] :> \[Epsilon] t[name] /. \[Epsilon]^n_ /; n > tmax :> 0;
    Print["Expanding Denominator",Now];
denExpansion = -Expand[(fde Normal[De[algebra, 1]])/x] /. 
      q^n_ /; n > M :> 0 /. 
     q -> Q[0] (Times @@ (ZZ^(FHighestRoot[algebra]) /. 
           ZtoTbasis)) /. 
    t[name__] :> \[Epsilon] t[name] /. \[Epsilon]^n_ /; n > tmax :> 0;
    Print["Expanding Ztop",Now];
Ztop = Series[
    Series[numExpansion/denExpansion, {Q[0], 0, M}] // 
     Normal, {\[Epsilon], 0, tmax}] // Normal // Expand;
     Print["Arranging the coefficients",Now];
     
     sol= CoefficientRules[Expand[Normal[x Ztop]/.\[Epsilon]->1],Join[{x,Q[0]},tt]];
    
   If[OptionValue[SavingPath]===False,_,
   	Print["Saving",Now];
	SetDirectory[OptionValue[SavingPath]];
	Export[OptionValue[FileName], Association[sol]];
   ];
   
   sol
   
      
]
   
End[] (* End Private Context *)

EndPackage[]
