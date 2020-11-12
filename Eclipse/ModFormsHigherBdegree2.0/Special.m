(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["Special`", {"CoefficientFixing`","DenominatorBaseDeg1`","Denominator`", "RootsHandling`", "NumeratorIndices`", "ModularRing`", "LieART`","WeylInvariantPolynomials`"}]
(* Exported symbols added here with SymbolName::usage *)  

SpecialSolve::usage="das ist good "

Begin["`Private`"] (* Begin Private Context *) 


Options[SpecialSolve]={SavingPath->False,FileName-> Null,bound->10,Shift->0,Tshift->False,debugging->False}



(* ::Subsubsection:: *)
(* Region Title *)


SpecialSolve[algebraexp_,algebra_(*gauge algebra*),trans_(*Transformation Rule*),nbase_ (*, inv_*),inst_,M_: M,OptionsPattern[]] := 
(* solve[algebra, M] =*) 
  Module[{df, fde, fullfact, gw,FandQ0factor,num,numsolved,numUnsolved,de,max,ff
     ,pn, tt,ZZ, tshift, \[Epsilon],jacsol,tbound,extrafactor,tboundMax,fullfactexpo,pnexpansion},
   Print["I am starting"];
   Print[Now];
   Off[Solve::svars]; (*To avoid the error message*)
   max=M;
   tt = Array[t[algebra,#]&, Rank[algebra]];
   ZZ = Array[Z[algebra,#]&,Rank[algebra]];

   fde = (Times @@ (ZZ^(##)) &@Total@LongRoots[algebra])/.ZtoTbasis/.trans//PowerExpand;
   If[OptionValue[Tshift]===False,
   	extrafactor=1; tshift=Table[0,Rank[algebra]],
   	extrafactor=Times@@(tt^OptionValue[Tshift]); tshift=OptionValue[Tshift]];
   
   If[OptionValue[debugging],Print[extrafactor, " and ", tshift]];
   
   ff[qorder2_]:=1/(Times @@ (ZZ^(FHighestRoot[algebra])))^((*(nbase-2)*)Max[0,nbase-2]- qorder2)/.ZtoTbasis/.trans//PowerExpand;
   
   fullfact[qorder2_] := extrafactor*
    fde/(Times @@ (ZZ^(FHighestRoot[algebra])))^((*(nbase-2)*)Max[0,nbase-2]- qorder2)/.ZtoTbasis/.trans//PowerExpand;
   fullfactexpo[qorder2_]:=Exponent[fullfact[qorder2]/.t[__]:>t,t];
    
   df=NumIndex[algebra,1,nbase]/2;
   Print["The degree and weight of the numerator are =",df," and ",NumWeight[algebra,1,nbase]];
   Print["I am starting to solve",Now];
   
   If[NumberQ[OptionValue[bound]],tbound[_]=OptionValue[bound],tbound[i_]:=OptionValue[bound][[i+1]]];
   (*This just gives the bound in a more convenient way*)
   
   tboundMax=Max[tbound/@Range[0,M]];
   
   
   Print["Getting the denominator",Now];
   de=Normal[De1[algebra,max]]/.q -> Q[0] (Times @@ (ZZ^(FHighestRoot[algebra])))/.(Table[Z[D5, i] -> (Z[D5, i] /. ZtoTbasis /. trans), {i, 1, 5}])/.t[name__] :> \[Epsilon] t[name];
      
   
   Print["Getting the invariants",Now];
   gw=Module[{cleanInst,ZtoTInvariants},
   cleanInst = Select[Normal[inst], #[[1]][[-1]] == 0 && #[[1]][[-2]] == 1 &]; (*Fixes the base degree to 1 and fiber to 0*)
   ZtoTInvariants[m__] := Join[expo[algebra] m[[1 ;; Rank[algebra]]], {m[[Rank[algebra] + 1]] +
     Max[nbase - 2,0]}, m[[Rank[algebra] + 2 ;; -1]]]; (* Writes the invariant in the t-basis, also takes care of the Q0 in the prefactor*)
   ZtoTInvariants[#[[1]]] -> #[[2]] & /@ cleanInst
   ];

	Print["Getting the numerator",Now];

   FandQ0factor=PowerExpand[FromCoefficientRules[gw,Join[tt,{Q[0],Qb,Qf}]]/. {Qb -> 1, Qf -> 0}/.trans] /. 
  t[name__] :> \[Epsilon] t[name]/.Q[0]^m_/;m>M:>0;
  
  
  pn[0]=With[{bound=fullfactexpo[0]-tbound[0]},
  	((Expand[# - Coefficient[#, \[Epsilon], 0] - \[Epsilon] Coefficient[#, \[Epsilon], 1]] &@
      Expand[(1/ff[0])(FandQ0factor/.Q[0]->0)(de/.Q[0]->0)]) /. (\[Epsilon]^
        n_ /; n > -bound :> 0)) /. \[Epsilon] -> 1];
  pn[1]=With[{bound=fullfactexpo[1]-tbound[1]},
  	((Expand[# - Coefficient[#, \[Epsilon], 0] - \[Epsilon] Coefficient[#, \[Epsilon], 1]] &@
      Expand[(1/ff[1])((FandQ0factor/.Q[0]->0)Coefficient[de,Q[0]]+Coefficient[FandQ0factor,Q[0]](de/.Q[0]->0))]) /. (\[Epsilon]^
        n_ /; n > -bound :> 0)) /. \[Epsilon] -> 1];
   (*
   pn[0]=Expand[(FandQ0factor/.Q[0]->0)(de/.Q[0]->0)]/.\[Epsilon]->1;
   pn[1]=Expand[(FandQ0factor/.Q[0]->0)Coefficient[de,Q[0]]+Coefficient[FandQ0factor,Q[0]](de/.Q[0]->0)]/.\[Epsilon]->1;
   *)
  (* pn=(FandQ0factor*de//Expand)/.Q[0]^m_/;m>M:>0/. \[Epsilon]^n_ /; n > tboundMax :> 0/.\[Epsilon]->1;*)
	(*Return[pn];*)

	Print["Solving in Weyl. pol.",Now];

	numsolved[qorder2_]:=numsolved[qorder2]=
	(PolyToWeylIncomplete[algebraexp,Expand[pn[qorder2]],Max[0,fullfactexpo[qorder2]-tbound[qorder2]]]);
  (* (PolyToWeylIncomplete[algebra,Expand[(1/ff[qorder2]) *(1/qorder2!)D[pn,{Q[0],qorder2}]/.Q[0]->0],Max[0,fullfactexpo[qorder2]-tbound[qorder2]]]);*)
(*This is the part that can actually be completely solved*)

	numUnsolved[qorder2_]:=  numUnsolved[qorder2]= givePoly2[algebraexp,fullfact[qorder2],df+qorder2,tbound[qorder2],{num,qorder2}];
   (*This is the part that cannot be solved with the invariants given*)

   num[qorder2_]:=num[qorder2]=
   numsolved[qorder2]
   (*This is the part that can actually be completely solved*)+
   numUnsolved[qorder2];
   (*This is the part that cannot be solved with the invariants given*)
   
   pnexpansion=Sum[q^m0 num[m0],{m0,0,M}];
   
   Print[fullfactexpo[#]-tbound[#]]&/@Range[0,M];
   
   Print["at level q^",#," I solved for ", Length[List@@Expand[numsolved[#]]]," coefficients and couldn't solve for ",
   Length[List@@Expand[numUnsolved[#]]]," coefficients"]&/@Range[0,M];
   
   Print[numsolved[#]]&/@Range[0,M];
   
   On[Solve::svars]; 
   
   Print["Got the solution ( ",Length[List@@Expand[pnexpansion]]," coeff) , will expand in Jacobi Forms"];
   Print[Now];
   jacsol=ExpandInJacobiForms[algebraexp,pnexpansion,df,NumWeight[algebra,1,nbase],M];
   
   Print["I am Done"];
   Print[Now];
 
   If[OptionValue[SavingPath]===False,_,
   	Print["Saving",Now];
	SetDirectory[OptionValue[SavingPath]];
	Export[OptionValue[FileName], jacsol];
   ];
   
   JacSol[algebra,nbase]=jacsol
   ]
   
End[] (* End Private Context *)

EndPackage[]
