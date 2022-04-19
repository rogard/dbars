(* :Title: Derivative Based Adaptive Rejection Sampling	*)
(* :Author: Erwann Rogard, Columbia University	*)
(* :Mathematica Version: 5.2			*)
(* :Sources:  
	[1] Gilks W.R. and Wild P., Adaptive Rejection Sampling for Gibbs Sampling, Applied Statistics, Vol.41, No.2. (1992) pp. 337-348
	[2] Wild P and Gilks W.R., Algorithm AS 287: Adaptive Rejection Sampling from Log-Concave Density Functions, Applied Statistics, Vol. 42, No.4. (1993), pp. 701-709
*)
(* :Discussion:
funEvalDer instead of {funEval,funDer} because computations within are likely to be shared for complicated densities.
*)
(*
:TODO:
- Separate the creation (make) from the initialization process, so that a same object can be reused for a different log-concave density
- Overflow mechanism. Although apparently not necessary with Mathematica
- Test with different distributions
*)

BeginPackage["DerivativeBasedAdaptiveRejectionSampling`",{"containers`","sharedNames`"}]

DerivativeBasedAdaptiveRejectionSampling/:
	DerivativeBasedAdaptiveRejectionSampling::usage="obj=Make[DerivativeBasedAdaptiveRejectionSampling,xlb,xInit,xub,funEvalDer]\nInverseCDF[obj,u]\nRandom[obj]\nClear[obj]\nNormalizingConst[obj]";


Begin["`Private`"]

(*---interface---*)
DerivativeBasedAdaptiveRejectionSampling/:	Make[DerivativeBasedAdaptiveRejectionSampling,args__]:=make[args];
invCumul=InverseCDF;
draw=Random;
clear=Clear;

(*---impl---*)
tangntExpression[x0_,val0_,der0_][x_]=val0+der0*(x-x0);
linejoinExpression[x0_,val0_,x1_,val1_][x_]=((x1-x)val0-(x0-x)val1)/(x1-x0);

ars::oob="`1` is out of bounds [`2`,`3`]";
ars::ub="unbounded domain [`1`,`2`] requires lowest/highest absicae, (`3`,`4`),to have +/- derivative, (`5`,`6`), respectively";
ars::zd="warning: zero derivative at `1` will fail invCum"
make[xlb_,xInit_?VectorQ,xub_,funEvalDer_]/;Length[xInit]>=2:=Module[
{object, ordering={}, x, eval, der,len=0, add, tangnt, linejoin, intrsctn, expTangntAddDivDer, expTangntSubDivDer, upperLog, lowerLog, map},
	(*Module[{i=0},(++i;x[i]=#;{eval[i],der[i]}=funEvalDer[#])&/@xInit];	*)

	add[xVal_,evalVal_,derVal_]/; Not[xlb<xVal<xub]:=(Message[ars::oob,xVal,xlb,xub];$Failed);
	add[xVal_,evalVal_,derVal_]/; Developer`ZeroQ[derVal]:=(Message[ars::zd,xVal];$Failed);
	add[xVal_,evalVal_,derVal_]:=(
		x[++len]=xVal; eval[len]=evalVal; der[len]=derVal;
		ordering=Ordering[x/@Range[len]];
	);

	object/:clear[object]:=
		(
			ClearAll/@
				Hold[
					object, ordering, x, eval, der, len, add, tangnt, linejoin, intrsctn, 
					expTangntAddDivDer, expTangntSubDivDer, upperLog, lowerLog, map
				]//ReleaseHold
		);(*TODO: verify*)

	add[#,Sequence@@funEvalDer[#]]&/@xInit;
	With[{il=ordering[[1]],iu=ordering[[len]]},
		If[ (xlb==-Infinity && der[ il ]<0) || (xub==Infinity && der[ iu ]>0), 
			Message[ars::ub,xlb,xub,x[il],x[iu],der[il],der[iu]]; $Failed
		]
	];

	tangnt[i1_]:=tangntExpression[x[i1],eval[i1],der[i1]];	
	linejoin[i1_,i2_]:=linejoinExpression[x[i1],eval[i1],x[i2],eval[i2]];
	intrsctn[i1_,i2_]:=intrsctn[i1,i2]=-(tangnt[i2][0]-tangnt[i1][0])/(der[i2]-der[i1]);
	expTangntAddDivDer[i1_,i2_]:=expTangntAddDivDer[i1,i2]=Exp[tangnt[i1][intrsctn[i1,i2]]]/der[i1];
	expTangntAddDivDer[i1_]:=expTangntAddDivDer[i1]=Exp[tangnt[i1][xub]]/der[i1];
	expTangntSubDivDer[i1_,i2_]:=expTangntSubDivDer[i1,i2]=Exp[tangnt[i1][intrsctn[i2,i1]]]/der[i1];
	expTangntSubDivDer[i1_]:=expTangntSubDivDer[i1]=Exp[tangnt[i1][xlb]]/der[i1];

	map[intrsctn,0]=xlb;
	map[intrsctn,i_/;i==len]:=xub;
	map[expTangntAddDivDer,i_/;i==len]:=expTangntAddDivDer[ordering[[i]]];
	map[op:(intrsctn|linejoin|expTangntAddDivDer),i_]:=op@@Extract[ordering,{{i},{i+1}}];
	map[expTangntSubDivDer,1]:=expTangntSubDivDer[ ordering[[1]] ];
	map[expTangntSubDivDer,i_]:=expTangntSubDivDer@@Extract[ordering,{{i},{i-1}}];
	map[op:(x|eval|der|tangnt),i_]:=op[ordering[[i]]];

	upperLog[zl_,zu_,i/; i>len][xVal_]:=$Failed;
	upperLog[zl_,zu_,i_][xVal_]/; (zl<=xVal<zu):=map[tangnt,i][xVal];
	upperLog[zl_,zu_,i_][xVal_]:=upperLog[zu,map[intrsctn,i+1],i+1][xVal];
	upperLog[][xVal_]:=upperLog[map[intrsctn,0],map[intrsctn,1],1][xVal];

	lowerLog[0, xl_,xu_][xVal_]/; xVal<xu=-Infinity;
	lowerLog[i_/; 1<=i<len,xl_,xu_][xVal_]/; xl<=xVal<xu:=map[linejoin,i][xVal];
	lowerLog[i_/; i<=len-2,xl_,xu_][xVal_]:=lowerLog[i+1,xu,map[x,i+2]][xVal];
	lowerLog[i_/; i==len-1,xl_,xu_][xVal_]/; xVal>=xu=-Infinity;
	lowerLog[i_,xl_,xu_][xVal_]=$Failed;
	lowerLog[][xVal_]:=lowerLog[0, map[intrsctn,0],map[x,1]][xVal];

	Module[{unnormlzdCumulIncr,normlzngConst},
		
		(* TODO: saving mechanism, as for intersctn*)
		unnormlzdCumulIncr[i_/; 1<=i<=len]:=(map[expTangntAddDivDer,i]-map[expTangntSubDivDer,i]);(*wrong*)

		normlzngConst[]:=Tr[unnormlzdCumulIncr/@Range[len]];
		object/: NormalizingConst[object]:=normlzngConst[];
		object/: invCumul[object,u_]:=Module[{cum,i=0,nc=normlzngConst[]},
			Module[{tmp=0}, While[tmp<nc*u,  cum=tmp; ++i; tmp+=unnormlzdCumulIncr[i]] ];
		(*	Print[
				"map[x,i]=",map[x,i],
				"\nmap[der,i]=",map[der,i],
				"\nmap[expTangntSubDivDer,i]=",map[expTangntSubDivDer,i],
				"\nmap[eval,i]=",map[eval,i],
				"\nnc*u=",nc*u
			]; *)
			map[x,i]+(
				Log[ map[der,i](map[expTangntSubDivDer,i]+(nc*u-cum))]-map[eval,i]
			)/map[der,i]
		];

	];
	
	Module[{xCandidate,acceptFirstPassQ=True, evalDer,upperLogTmp,u1,u2,u3},
		object/: draw[object]:=
			(
				doWhile[
					If[Not[acceptFirstPassQ],add[xCandidate,Sequence@@evalDer]];	
					xCandidate=invCumul[object,(u1=Random[]; (*Print["u1=",u1];*) u1)],
					acceptFirstPassQ=(
						(u2=Random[]; (*Print["u2=",u2];*) u2)<=Exp[lowerLog[][xCandidate]-(upperLogTmp=upperLog[][xCandidate])]
					); (*Print["xCandidate=",xCandidate,"lowerLog[]",lowerLog[][xCandidate],"upperLogTmp=",upperLogTmp];*)
					Not[ 
						acceptFirstPassQ 
						|| (u3=Random[]; (*Print["u3=",u3];*) u3<=Exp[(evalDer=funEvalDer[xCandidate])[[1]]-upperLogTmp]) 
					]
				];
				Return[xCandidate]
			);
	];
	object
];

(*-------misc---------*)
Attributes[doWhile] = {HoldAll} 
doWhile[body_, test_] := (body; While[test, body])(*Section 7.2.1, Wagner D.B., Power Programming with Mathematica, 1996 *);

End[]

EndPackage[]
(*
Needs/@{"DerivativeBasedAdaptiveRejectionSampling`","Graphics`Graphics`",
    "Statistics`ContinuousDistributions`","ProbabilityPlot`"}

{Null,Null,Null,Null}

(*---INTRO---*)

(* In this notebook we test the package \
DerivativeBasedAdaptiveRejectionSampling for the standard normal distribution \
*)

(*---SETTINGS---*)

(*--PERMANENT SETTINGS--*)

updf[x_]=-x^2/2;
derpdf[x_]=D[updf[x],x];
fun[x_]:=Through[{updf,derpdf}[x]];
trueInvCumul[u_]=
    x/.Solve[Integrate[Exp[updf[y]]/Sqrt[2*Pi],{y,-Infinity,x}]\[Equal]u,
          x][[1]];
trueNC=Sqrt[2 Pi]//N;

(*--USER SETTINGS--*)

repsCnt=10^2;
lowerInit = -0.5;
upperInit = 1.5;

(*---DATA GENERATION--*)

(*-INDEPENDENT DRAWS USING A SEQUENCE OF APPROXIMATIONS-*)

ClearAll[data,NCs,LogPDFplot,invCumulPlot,probPlot,NCplot]
data[0]={};
NCs[0]={};
LogPDFplot;
invCumulPlot;
probPlot;
NCplot;
Module[{obj,lowerLog,upperLog},
    obj=Make[
        DerivativeBasedAdaptiveRejectionSampling,-Infinity,{lowerInit,
          upperInit},Infinity,fun];
    lowerLog=ToExpression[Last[Names["*`lowerLog$*"]]];
    upperLog=ToExpression[Last[Names["*`upperLog$*"]]];
    SeedRandom[0];
    Do[data[0]={data[0],Random[obj]};
      NCs[0]={NCs[0],NormalizingConst[obj]},{repsCnt}];
    data[0]=Flatten[data[0]];
    NCs[0]=Flatten[NCs[0]];
    NCPlot[0]=
      ListPlot[NCs[0],PlotRange\[Rule]{Automatic,{trueNC,Max[NCs[0]]}}];
    LogPDFplot[0]=
      Plot[{lowerLog[][x],updf[x],upperLog[][x]},{x,-1.9,1.9},
        PlotStyle\[Rule]{Blue,Black,Red},DisplayFunction\[Rule]Identity];
    invCumulPlot[0]=
      Plot[{trueInvCumul[u],InverseCDF[obj,u]},{u,0.001,0.9999},
        DisplayFunction\[Rule]Identity];
    probPlot[0]=ProbabilityPlot[data[0],trueInvCumul];
    ];

(*Show[GraphicsArray[(Histogram[#1,DisplayFunction\[Rule]Identity]&)/@{toto,
              RandomArray[NormalDistribution[0,1],1000]}]]*(dta=toto);*)

(*-INDEPENDENT DRAWS-*)

data[1]={};
Module[{repsCnt=10^3,r,mean=0,var=0},
    Do[
      Module[{obj},
        obj=
          Make[DerivativeBasedAdaptiveRejectionSampling,-Infinity,{lowerInit,
              upperInit},Infinity,fun];
        r=Random[obj];
        data[1]={data[1],r};
        ];
      mean+=r;
      var+=r^2;
      clear[obj];
      ,{repsCnt}
      ];
    data[1]=Flatten[data[1]];
    probPlot[1]=ProbabilityPlot[data[1],trueInvCumul];
    mean/=repsCnt;
    var-=repsCnt mean^2;
    var/=(repsCnt-1);
    Return[{mean,var}];
    ];

(*---OUTPUT---*)

(*-INDEPENDENT DRAWS FROM A SEQUENCE OF APPROXIMATIONS-*)

Show[NCPlot[0],DisplayFunction\[Rule]$DisplayFunction,
  PlotLabel\[Rule]"Sequence of normalizing constants"]
Show[LogPDFplot[0],DisplayFunction\[Rule]$DisplayFunction,
  PlotLabel\[Rule]"PDF and lower/upper approximations"]
Show[invCumulPlot[0],DisplayFunction\[Rule]$DisplayFunction,
  PlotLabel\[Rule]"Inverse cumulative"]
Show[probPlot[0],DisplayFunction\[Rule]$DisplayFunction,
    PlotLabel\[Rule]"qqplot"];

(* INDEPENDENT DRAWS *)

*)
