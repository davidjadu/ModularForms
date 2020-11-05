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

givePoly2[algebra_,fact_,degree_,bound_,label_]:=Module[{factexpos,aa,sols},
	factexpos=CoefficientRules[fact, Array[t[algebra, #] &, Rank[algebra]]][[All, 1]][[1]];
	aa=Array[a,Rank[algebra]];
	sols=Solve[factexpos>= aa.tInvExpos[algebra] && Total[factexpos- aa.tInvExpos[algebra]]>bound && aa >= 0 && Total[aa]<=degree, aa, Integers];
	If[sols=={},0,Total[k[label,aa]Product[p[i]^a[i],{i,1,Rank[algebra]}]/.sols]]
]

(* ::Subsubsection:: *)
(* Region Title *)


Options[solve]={SavingPath->False,FileName-> Null,bound->10,Shift->0,Tshift->False,debugging->False}



(* ::Subsubsection:: *)
(* Region Title *)


solve[algebra_,nbase_ (*, inv_*),inst_,M_: M,OptionsPattern[]] := 
(* solve[algebra, M] =*) 
  Module[{df, fde, fullfact, gw,
    NumberofTerms,FandQ0factor,toSolve,sol,num,numsolved,numUnsolved,
     Pde,pnAnsatz,pn, tt,ZZ, tshift,ntnt,nt, \[Epsilon], FullSol,index,jacsol,tbound,extrafactor,tboundMax,fullfactexpo,pnexpansion},
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
   fullfactexpo[qorder2_]:=Exponent[fullfact[qorder2]/.t[__]:>t,t];
    
   df=NumIndex[algebra,1,nbase];
   Print["The degree and weight of the numerator are =",df," and ",NumWeight[algebra,1,nbase]];
   Print["I am starting to solve",Now];
   
   If[NumberQ[OptionValue[bound]],tbound[_]=OptionValue[bound],tbound[i_]:=OptionValue[bound][[i+1]]];
   (*This just gives the bound in a more convenient way*)
   
   tboundMax=Max[tbound/@Range[0,M]];
   
   
   Print["Getting the denominator",Now];
   Pde=
       Series[Coefficient[
          fde (Series[De[algebra,1,nbase] // Normal, {q, 0, M}] // 
               Normal) /. 
            q -> Q[0] (Times @@ (ZZ^(FHighestRoot[algebra])/.ZtoTbasis)) /. 
           t[name__] -> \[Epsilon] t[name], x], {\[Epsilon], 0, tboundMax}] // 
      Normal;
      
   
   Print["Getting the invariants",Now];
   gw=Module[{cleanInst,ZtoTInvariants},
   cleanInst = Select[Normal[inst], #[[1]][[-1]] == 0 && #[[1]][[-2]] == 1 &]; (*Fixes the base degree to 1 and fiber to 0*)
   ZtoTInvariants[m__] := Join[expo[algebra] m[[1 ;; Rank[algebra]]], {m[[Rank[algebra] + 1]] +
     nbase - 2}, m[[Rank[algebra] + 2 ;; -1]]]; (* Writes the invariant in the t-basis, also takes care of the Q0 in the prefactor*)
   ZtoTInvariants[#[[1]]] -> #[[2]] & /@ cleanInst
   ];

	Print["Getting the numerator",Now];

   FandQ0factor=FromCoefficientRules[gw,Join[tt,{Q[0],Qb,Qf}]]/. {Qb -> 1, Qf -> 0} /. 
  t[name__] :> \[Epsilon] t[name];
   
   pn=(FandQ0factor*Pde//Expand)/.Q[0]^m_/;m>M:>0/. \[Epsilon]^n_ /; n > tboundMax :> 0/.\[Epsilon]->1;

	Print["Solving in Weyl. pol.",Now];

	numsolved[qorder2_]:=numsolved[qorder2]=
   (PolyToWeylIncomplete[algebra,Expand[fullfact[qorder2]^-1 *(1/qorder2!)D[pn,{Q[0],qorder2}]/.Q[0]->0],Max[0,fullfactexpo[qorder2]-tbound[qorder2]]]);
(*This is the part that can actually be completely solved*)

	numUnsolved[qorder2_]:=  numUnsolved[qorder2]= givePoly2[algebra,fullfact[qorder2],df+qorder2,tbound[qorder2],{num,qorder2}];
   (*This is the part that cannot be solved with the invariants given*)

   num[qorder2_]:=num[qorder2]=
   numsolved[qorder2]
   (*This is the part that can actually be completely solved*)+
   numUnsolved[qorder2];
   (*This is the part that cannot be solved with the invariants given*)
   
   pnexpansion=Sum[q^m0 num[m0],{m0,0,M}];
   
   Print["at level q^",#," I solved for ", Length[List@@Expand[numsolved[#]]]," coefficients and couldn't solve for ",
   Length[List@@Expand[numUnsolved[#]]]," coefficients"]&/@Range[0,M];
   
   On[Solve::svars]; 
   
   Print["Got the solution ( ",Length[List@@Expand[pnexpansion]]," coeff) , will expand in Jacobi Forms"];
   Print[Now];
   jacsol=ExpandInJacobiForms[algebra,pnexpansion,df,NumWeight[algebra,1,nbase],M];
   
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
