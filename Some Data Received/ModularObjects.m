(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["ModularObjects`"]

initializeModularObjects::usage = "initializeModularObjects[qmax] needs to be run before calling any functions yielding q expansions of modular objects"
getPhi::usage =
"getPhi[weight,index] stores all elements of given weight and index of the module of Weyl invariant Jacobi forms over the ring of modular forms in the variable Jaclist. It returns the length of this list. It requires wiGens and rank."
expressInTermsOfGenerators::usage = 
"expressInTermsOfGenerators[genList,phi1] expresses phi1 in terms of the Weyl invariant polynomials given in genList. The constant polynomial is not assumed."
phiInv::usage = 
"phiInv[genList,phi] calls expressInTermsofGenerators on the coefficients of phi in an expansion in q up to qmax as set by intializeModularObjects."
expandinWeylInvJac::usage =
"expandinWeylInvJac[phi,weight,index] expands phi, a polynomial in q of order qmax with coefficients in Weyl invariant polynomials in Weyl invariant Jacobi forms of indicated weight and index. The Jacobi forms are assumed given in the variable PhiPre. expandinWeylInvJac[phiRaw_,phiGspec_,weight_,index_] creates PhiPre based on the name of Weyl invariant Jacobi forms specified in phiGspec: the forms should be given as phiGspec[0] to phiGspec[rank]."

initializeModularObjects[qm_]:=Module[{},
	qmax=qm;
	qthetamax=Ceiling[Sqrt[2qmax]];
	etas=q^(1/24) Product[1-q^n,{n,1,qmax}];
	etats=Product[1-q^n,{n,1,qmax}];
	E2s=Normal[Simplify[Series[1-24*Sum[n*q^n/(1-q^n),{n,1,qmax+1}],{q,0,qmax}]]];
	E4s=Normal[Simplify[Series[1+240*Sum[n^3*q^n/(1-q^n),{n,1,qmax+1}],{q,0,qmax}]]];
	E6s=Normal[Simplify[Series[1-504*Sum[n^5*q^n/(1-q^n),{n,1,qmax+1}],{q,0,qmax}]]];
	subEq={E2-> E2s, E4-> E4s, E6-> E6s,eta-> etas,etat-> etats};
	theta11=Sum[q^(1/2 (n+1/2)^2) y^(n+1/2) (-1)^(n+1/2),{n,-qthetamax,qthetamax}];
	theta10=Sum[q^(1/2 (n+1/2)^2) y^(n+1/2),{n,-qthetamax,qthetamax}];
	theta00=Sum[q^(1/2 n^2) y^n,{n,-qthetamax,qthetamax}];
	theta01=Sum[q^(1/2 n^2) y^n (-1)^n,{n,-qthetamax,qthetamax}];
	theta1=-theta11;theta2=theta10;theta3=theta00;
	theta4=theta01;
	thetaTau=(#/.y-> 1)&/@{theta1,theta2,theta3,theta4};
	wp=(thetaTau[[3]]^2 thetaTau[[2]]^2)/4 theta4^2/theta1^2-1/12 (thetaTau[[3]]^4+thetaTau[[2]]^4);
	wps=Series[wp,{q,0,qmax}]//Normal//Simplify;
(* x1 = (2 sin(z/2))^2 ,  y = exp[iz] , Ax = -( Subscript[\[Theta], 1]/\[Eta]^3)^2*)
	Ax=-x1 Series[Product[(1+x1 q^n-2q^n+q^(2n))^2/(1-q^n)^4,{n,1,qmax}],{q,0,qmax}]//Normal;];

subtheta={Subscript[\[Theta], 1][a[sck_]]:>  (theta1/.y-> X[sck]),\[Eta]:>  etas};

mat[b_,n_]:=Module[{},
firstColumn=p[#,0]&/@Range[b,n];setfCtoOne=#-> 1&/@firstColumn;Outer[p,Range[b,n],Range[0,n-b]]/.setfCtoOne];

qdwp[n_]:=Module[{},
expanswp=p[0,#]&/@Range[1,n];Collect[Det[mat[0,n]]/Det[mat[1,n]]//Expand,expanswp]];

yDy[f_,deg_]:=Module[{},
	Nest[y D[#,y]&,f,deg]];

yDy[f_,deg_,j_]:=Module[{},
	Nest[y D[#,y]&,f,deg]/.y-> X[j]];

subwp={Derivative[sck_][\[WeierstrassP]][a[scj_]]:> ( yDy[wps,sck]/.y-> X[scj]),\[WeierstrassP][a[scj_]]:> ( wps/.y-> X[scj])};

genSeriesAn[n_]:=Module[{},
	(-1)^(n+1)/n! Product[Subscript[\[Theta], 1][a[i]]/(I \[Eta]^3),{i,1,n+1}]qdwp[n]];

phiAn[n_,m_]:=Module[{},
	genS=genSeriesAn[n];
	subPretty=p[sck_,scl_]-> Derivative[scl-1][\[WeierstrassP]][a[sck]];
	phiRaw=If[m>0,Coefficient[genS,p[0,m]],genS/.p[0,sck_]-> 0];
	phiRaw/.subPretty//Simplify];
	phiAnX[n_,k_]:=Module[{i},
	subExp=X[n+1]-> 1/Product[X[i],{i,1,n}];
	phi=phiAn[n,k];
	phiSub=phi/.subtheta/.subwp/.subExp;
	phiS=PowerExpand[Normal[Series[phiSub,{q,0,qmax}]]];
	phiSCL=Together[CoefficientList[phiS,q]];
	Sum[phiSCL[[i]]q^(i-1),{i,1,Length[phiSCL]}]];

phiG2X[k_]:=Module[{n},
	If[k==2,Collect[Expand[phiAnX[2,2]^2]/.Power[q,n_]/;n>qmax-> 0,q],phiAnX[2,k]]];

subA3toC3={X[1]-> Sqrt[X[3]/(X[1]X[2])],X[2]-> Sqrt[X[1]/(X[2]X[3])],X[3]-> Sqrt[X[2]/(X[1]X[3])]};

(phiC3X[#-1]:=({phiAnX[3,0],phiAnX[3,1],phiAnX[3,3]}[[#]]/.subA3toC3)//Expand//PowerExpand)&/@Range[3];

phiC3X[3]:=Normal[phiAnX[3,2]^2+O[q]^(qmax+1)]/.subA3toC3//Expand//PowerExpand;

phiD4X[0]:=phiD4X[0]=Collect[Simplify[PowerExpand[Normal[Series[1/etas^12 (thetaTau[[3]]^8 Product[theta3/.y-> X[i],{i,1,4}]-thetaTau[[4]]^8 Product[theta4/.y-> X[i],{i,1,4}]-thetaTau[[2]]^8 Product[theta2/.y-> X[i],{i,1,4}]),{q,0,qmax}]]]],q];

phiD4X[1]:=phiD4X[1]=Collect[Simplify[PowerExpand[Normal[Series[1/etas^12 ((thetaTau[[4]]^4-thetaTau[[2]]^4)Product[theta3/.y-> X[i],{i,1,4}]-(thetaTau[[2]]^4+thetaTau[[3]]^4)Product[theta4/.y-> X[i],{i,1,4}]+(thetaTau[[3]]^4+thetaTau[[4]]^4)Product[theta2/.y-> X[i],{i,1,4}]),{q,0,qmax}]]]],q];

phiD4X[2]:=phiD4X[2]=Collect[Simplify[PowerExpand[Normal[Series[1/etas^12 (Product[theta3/.y-> X[i],{i,1,4}]-Product[theta4/.y-> X[i],{i,1,4}]-Product[theta2/.y-> X[i],{i,1,4}]),{q,0,qmax}]]]],q];

phiD4X[3]:=phiD4X[3]=Collect[Simplify[PowerExpand[Normal[Series[1/etas^12 Product[theta1/.y-> X[i],{i,1,4}],{q,0,qmax}]]]],q];

phiD4X[4]:=phiD4X[4]=Cancel[Collect[Simplify[PowerExpand[Normal[Series[1/etas^24 Product[theta1^2/.y-> X[i],{i,1,4}]Sum[wps/.y-> X[i],{i,1,4}],{q,0,qmax}]]]],q]];

together[f_]:=Module[{i,l},
	fC=Together[CoefficientList[f,q]];
	l=Length[fC];
	Sum[q^(i-1) fC[[i]],{i,1,l}]];

together[f_,l_]:=Module[{i},
	fC=Together[CoefficientList[f,q]];
	Sum[q^(i-1) fC[[i]],{i,1,l+1}]]

simplify[F_,f_,l_]:=Module[{i},
	fC=F[CoefficientList[f,q]];
	Sum[q^(i-1) fC[[i]],{i,1,l+1}]];

genSeriesBn[n_]:=Module[{},
	Product[(Subscript[\[Theta], 1][a[i]]/\[Eta]^3)^2,{i,1,n}]qdwp[n]];

phiBn[n_]:=Module[{},
	genS=(Subscript[\[Theta], 1][a[0]]/\[Eta]^3)^(2n) genSeriesBn[n];
	subPretty=p[sck_,scl_]-> Derivative[2(scl-1)][\[WeierstrassP]][a[sck]];
	genS/.subPretty//Simplify];

phiBn[n_,m_]:=Module[{},
	genS=genSeriesBn[n];
	subPretty=p[sck_,scl_]-> Derivative[2(scl-1)][\[WeierstrassP]][a[sck]];
	phiRaw=If[m>0,Coefficient[genS,p[0,m]],genS/.p[0,sck_]-> 0];
	phiRaw/.subPretty//Simplify];

phiBnX[n_,k_]:=Module[{i,phi},
phi=phiBn[n,k];phiT=Together[phi];num=Numerator[phiT];denom=Denominator[phiT];numSub=num/.subtheta/.subwp;denomSub=denom/.subtheta/.subwp;numS=PowerExpand[Normal[Series[numSub,{q,0,qmax+1}]]];denomS=PowerExpand[Normal[Series[denomSub,{q,0,qmax+1}]]];phiS=PowerExpand[Normal[Series[numS/denomS,{q,0,qmax}]]];phiSCL=Together[CoefficientList[phiS,q]];Sum[phiSCL[[i]]q^(i-1),{i,1,Length[phiSCL]}]];

sumList[sL_]:=Sum[c[i]sL[[i]],{i,1,Length[sL]}];
sumList[sL_,varname_]:=Sum[varname[i]sL[[i]],{i,1,Length[sL]}];

getPoly[order_]:=Module[{i,k},
	numberOfTerms=1;
	ansatz=c[0][1];
	For[i=1,i<= order,i++,		
	monomsRaw=IntegerPartitions[i,All, Range[rank]];
	numberOfTerms=numberOfTerms+Length[monomsRaw];
	monoms=Product[p[k]^Count[#,k],{k,1,rank}]&/@monomsRaw;
	ansatz=ansatz+sumList[monoms,c[i]]];
	ansatz];

getPolyP[order_]:=Module[{i},
	ansatz=c[0][1];
	For[i=1,i<= order,i++,
	monomsRaw=IntegerPartitions[i,All,Range[rank]];
	monoms=Product[P[k]^Count[#,k],{k,1,rank}]&/@monomsRaw;
	ansatz=ansatz+sumList[monoms,c[i]]];
	ansatz];

getPolyInd[index_]:=Module[{i},
	numberOfTerms=1;
	ansatz=c[0][1];
	For[i=1,i<= index,i++,
	monomsRaw=Flatten[Permutations[#]&/@IntegerPartitions[i,{rank},Range[0,i]],1];
	numberOfTerms=numberOfTerms+Length[monomsRaw];
	monoms=Product[p[k]^#[[rank+1-k]],{k,1,rank}]&/@monomsRaw;
	ansatz=ansatz+sumList[monoms,c[i]]];
	ansatz];

getPolyIndP[index_]:=Module[{i},
numberOfTerms=1;
ansatz=c[0][1];
For[i=1,i<= index,i++,
monomsRaw=Flatten[Permutations[#]&/@IntegerPartitions[i,{rank},Range[0,i]],1];
numberOfTerms=numberOfTerms+Length[monomsRaw];
monoms=Product[P[k]^#[[rank+1-k]],{k,1,rank}]&/@monomsRaw;
ansatz=ansatz+sumList[monoms,c[i]]];
ansatz];

getPolyInv[philist_]:=Module[{cl,cl01,x},
JaclistE=Jaclist/.subPhi/.subEqQ;JacQ=CoefficientList[Plus@@JaclistE,q][[orderQ+1]];cl=CoefficientList[JacQ,PList];cl01=cl/.x_/;!(x==0)-> 1;invList=List@@Expand[Internal`FromCoefficientList[cl01,PList]];numberOfTerms=Length[invList];Plus@@(d[#]invList[[#]]&/@Range[Length[invList]])];

expressInTermsOfGenerators[genList_, expr_]:=Module[{},
nGens=Length[genList]-1;If[genList[[1]]==1,subP0={P[0]-> 1},subP0={}];fracPow=If[(fractionalGens=Denominator[#]&/@Select[Flatten[Exponent[genList,X[#]]&/@Range[rank]],0<#<1&])=={},1,LCM@@(fractionalGens)];XtoY=X[#]-> Y[#]^fracPow&/@Range[rank];YList=Y[#]&/@Range[rank];PList=P[#]&/@Range[0,nGens];genListY=genList/.XtoY//Expand//PowerExpand;exprY=expr/.XtoY//Expand//PowerExpand;MaxYinExpr=Exponent[exprY,Y[#]]&/@Range[rank];subPgen=P[#]-> genListY[[#+1]]&/@Range[0,nGens];order=Max[Exponent[exprY,Y[#]]&/@Range[rank]];prodOfgens=Sequence@@(PList&/@Range[order]);linGenList=DeleteDuplicates[Flatten[Outer[Times,prodOfgens]]/.subP0];subPmaxY=Outer[Log[P[#2]]-> Max[Exponent[genListY[[#2+1]],Y[#1]]]&,Range[rank],Range[rank]];MaxPofY=(Log[#]&/@linGenList//PowerExpand)/.subPmaxY;posD=Position[MaxPofY[[1]],_?(#>MaxYinExpr[[1]]&)];linGenList=Delete[linGenList,posD];nLGens=Length[linGenList];genPolyP=Plus@@(c[#]linGenList[[#]]&/@Range[nLGens]);genPoly=genPolyP/.subPgen//Expand//PowerExpand;SolveAlways[genPoly==exprY,YList][[1]]];

phiInv[genList_,phi_]:=Module[{i},
	phiCL=CoefficientList[phi,q];
	lenQ=Length[phiCL];
	solList={expressInTermsOfGenerators[genList,#],genPolyP}&/@phiCL;
	phiInvCL=(#[[2]]/.#[[1]])&/@solList;
	phiInvCLq=phiInvCL[[#]]q^(#-1)&/@Range[lenQ];
	Plus@@phiInvCLq];

phiInvNorm[genList_,phi_]:=Module[{},
phiI=phiInv[genList,phi];norm=If[Or[(normT=Coefficient[phiI/.q-> 0,P[rank]])===0,Not[NumberQ[normT]]],1,normT];Cancel[phiI/norm]];

(* getPhi yields a list of Weyl invariant Jacobi forms, in the variable Jaclist, of indicated weight and index. It requires the variables rank and wiGens.*)
getPhi[weight_,index_]:=Module[{i,j,w,l},
weightG[mults_]:=Sum[mults[[i]]wiGens[[i]][[1]],{i,1,rank+1}];Jaclist={};NofT=0;iGs=0;iGauge=index;w=weight;
(* distribution of Gs index between A and B *)
distInGs={#,iGs-#}&/@Range[0,iGs];
(* distribution of gauge index between rankB31+1 generators, all of index 1 would be the following simple command*)
(* distInGauge=Flatten[Permutations[#]&/@IntegerPartitions[iGauge,{rank+1},Range[0,iGauge]],1];*)
(* With total index say 10, and indices 1,1,1,2, we first see how to partition 10 into 1's and 2's. Next we distribute the number of 1's among three phis with index 1, and the number of 2's among 1 phi of index 2.*)distInGauge=distributeIndex[iGauge];
phis=Flatten[Outer[Join,distInGs,distInGauge,1],1];Phis=(A^#[[1]] B^#[[2]] Product[Phi[i]^#[[i+2]],{i,1,rank+1}])&/@phis;weightPhis=(weightG[Take[#,-(rank+1)]]-2#[[1]])&/@phis;weightEisenstein=(w-weightPhis);posElligiblePhis=Position[weightEisenstein,_?(#>= 0&),1];elligiblePhis=Flatten[Phis[[#]]&/@posElligiblePhis];weightEisenstein=Flatten[weightEisenstein[[#]]&/@posElligiblePhis];distwEis=IntegerPartitions[#,All,{4,6}]&/@weightEisenstein;For[i=1,i<= Length[elligiblePhis],i++,
eis=distwEis[[i]];Eisensteins=E4^Count[#,4] E6^Count[#,6]&/@eis;monomContr=elligiblePhis[[i]]Eisensteins;Jaclist=Flatten[Append[Jaclist,monomContr]]];Length[Jaclist]];

distributeIndex[index_]:=Module[{},
indices=wiGens[[#]][[2]]&/@Range[rank+1];diffIndices=DeleteDuplicates[indices];multInd=Count[indices,#]&/@diffIndices;freqIndinPart=Outer[Count,IntegerPartitions[index,All,diffIndices],diffIndices,1];
(* f will be used to create a list {{first index n times, second index m times, ...}, {..}}. *)
f[x_,y_]:={x[[y]],multInd[[y]]};distInGaugeF[howMany_,amongHowMany_]:=Flatten[Permutations[#]&/@IntegerPartitions[howMany,{amongHowMany},Range[0,howMany]],1];almostThere=Map[distInGaugeF[Sequence@@#]&,Outer[f,freqIndinPart,Range[Length[diffIndices]],1],{2}];distInGauge=Flatten[toFlatten=Outer[Join,Sequence@@#,1]&/@almostThere,Depth[toFlatten]-3]];

expandinWeylInvJac[phiRaw_,weight_,index_]:=Module[{},
If[Not[ValueQ[phiPre[1]]],Print["Need to run routine with name of Weyl invariant Jacobi forms indicated."];Abort[]];solJ={};numFullSolve=0;orderQ=-1;NoT=getPhi[weight,index];While[(!(NoT==numFullSolve))&& orderQ<qmax,orderQ=orderQ+1;subOrdQ=If[orderQ==0,{q-> 0},{q^n_/;n> orderQ-> 0}];(phiGE[#]=phiPre[#]/. subOrdQ)&/@Range[0,rank];subPhi={Phi[gN_]:>  (phiGE[gN-1])};subEqQ=(subEq/.subOrdQ);numJE={};time=Timing[Monitor[For[i=1,i<= Length[Jaclist],i++,JacEv=Expand[Jaclist[[i]]/.subPhi/.subEqQ/.subOrdQ]/.subOrdQ;JacEvq=If[orderQ>0,Coefficient[JacEv,q^orderQ],JacEv];numJE=Join[numJE,{c[i]JacEvq}]],i]];numJEsum=Plus@@numJE/.solJ;phiRawQ=SeriesCoefficient[phiRaw,{q,0,orderQ}];PiCL=Flatten[CoefficientList[numJEsum-phiRawQ,PList]];eqs=#==0&/@PiCL;cList=c[#]&/@Range[NoT];time=Timing[solJo=Solve[eqs,cList]];If[solJo=={},Print["No solutions at order: ", orderQ];Abort[],solJo=solJo[[1]]];solJ=Join[solJ,solJo];RHSsolJ=Values[Association[solJ]];numFullSolve=Count[RHSsolJ,_?NumberQ]];Plus@@(c[#]Jaclist[[#]]&/@Range[NoT])/.solJ];

expandinWeylInvJac[phiRaw_,phiGspec_,weight_,index_]:=Module[{},
phiG[n_]:=phiGspec[n];genList=Join[{1},p[#]&/@Range[rank]];(phiPre[#]=phiInvNorm[genList,phiG[#]])&/@Range[0,rank];solJ={};numFullSolve=0;orderQ=-1;NoT=getPhi[weight,index];While[(!(NoT==numFullSolve))&& orderQ<qmax,orderQ=orderQ+1;subOrdQ=If[orderQ==0,{q-> 0},{q^n_/;n> orderQ-> 0}];(phiGE[#]=phiPre[#]/. subOrdQ)&/@Range[0,rank];subPhi={Phi[gN_]:>  (phiGE[gN-1])};subEqQ=(subEq/.subOrdQ);numJE={};time=Timing[Monitor[For[i=1,i<= Length[Jaclist],i++,JacEv=Expand[Jaclist[[i]]/.subPhi/.subEqQ/.subOrdQ]/.subOrdQ;JacEvq=If[orderQ>0,Coefficient[JacEv,q^orderQ],JacEv];numJE=Join[numJE,{c[i]JacEvq}]],i]];numJEsum=Plus@@numJE/.solJ;phiRawQ=SeriesCoefficient[phiRaw,{q,0,orderQ}];PiCL=Flatten[CoefficientList[numJEsum-phiRawQ,PList]];eqs=#==0&/@PiCL;cList=c[#]&/@Range[NoT];time=Timing[solJo=Solve[eqs,cList]];If[solJo=={},Print["No solutions at order: ", orderQ];Abort[],solJo=solJo[[1]]];solJ=Join[solJ,solJo];RHSsolJ=Values[Association[solJ]];numFullSolve=Count[RHSsolJ,_?NumberQ]];Plus@@(c[#]Jaclist[[#]]&/@Range[NoT])/.solJ];

EndPackage[]
