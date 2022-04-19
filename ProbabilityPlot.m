(* :Title: Probability Plot			*)
(* :Author: Erwann Rogard, Columbia University	*)
(* :Mathematica Version: 5.2			*)
(* :Discussion:  maybe some built-in functions from Statistics` more suitable within this program *)
BeginPackage["ProbabilityPlot`",{"CustomTicks`"}]

ProbabilityPlot/: ProbabilityPlot::usage="ProbabilityPlot[data_?VectorQ, invCumul_]";

Begin["`Private`"]

Module[{inputTo, opts},
    inputTo[data_?VectorQ, invCumul_] := 
      With[{den = Length[data] + 1}, 
        Module[{i = 0}, {#, invCumul[++i/den]} & /@ Sort[data]]];
    ProbabilityPlot[data_?VectorQ, invCumul_] :=
      Module[{in = inputTo[data, invCumul], min, max},
        {min, max} = Through[{Min, Max}[Flatten[in]]]; 
        {ListPlot[in, AspectRatio -> 1, DisplayFunction -> Identity], 
            Graphics[Line[{{min, min}, {max, max}}], AspectRatio -> 1]}
          // 
          Show[#, TextStyle -> {FontFamily -> "Times"}, 
              DisplayFunction -> Identity, 
              Ticks -> {LinTicks[min, max], LinTicks[min, max]}] &
	];
];
End[]
EndPackage[]
