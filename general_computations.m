Clear["Global`*"];

(* ------------------------------------------------------------------------- *)
(* auxiliary functions for calculus *)
LieDerive[v_List,w_List,var_List]:=Transpose[D[w,#]& /@ var] . v /; \
    Length[v] == Length[var]

LieBracket[v_List,w_List,var_List]:=LieDerive[w,v,var]-LieDerive[v,w,var] /; \
    Length[v] == Length[w] == Length[var]

PoissonBracket[f_, g_, q_List, p_List] /; Length[q] == Length[p] := \
    Total@Flatten@Fold[List,0,MapThread[D[f, #1] D[g, #2] - D[f, #2] D[g, #1] &,\
    {q, p}]]

EliminTe[expr_,var_List,ordre_Integer]:=Module[{},\
    FromCoefficientRules[Select[CoefficientRules[expr, var], \
    Total@#[[1]] <= ordre &], var]]

mTaylor[expr_,var_List,pts_List,ord_Integer] /; Length[var] == Length[pts] := \
    If[ord!=0,Normal[Series[(expr /. Thread[var -> ssss (var - pts) + pts])\
    //ExpandAll, {ssss, 0, ord}]] /. {ssss -> 1},expr]

IntSmallTime[VF_List,var_List,qf_List,ord_Integer]:= qf + \
    Sum[ttt^k/ k! Nest[LieDerive[VF,#,var]&,VF,k-1],{k,1,ord}]/.Thread[var->qf] 

PushForward[XX_List,ff_,invf_,xxx_List]:=Module[{zzz=Table[Subscript[z,i],\
    {i,1,Length[xxx]}]},dfx=Outer[D,ff[xxx],xxx];((dfx . XX)/. \
    Thread[xxx->invf[zzz]])/. Thread[zzz->xxx]];

PullBack[XX_List,ff_,xxx_List,yyy_List]:=Module[{},dfy=Outer[D,ff[yyy],yyy];
    Inverse[dfy] . (XX /. Thread[xxx->ff[yyy]])];

leadingSeries[expr_, {x_, x0_}] := Normal[
    expr /. x -> Series[x, {x, x0, 1}] /.\
    Verbatim[SeriesData][a__, {b_, ___}, c__] :> SeriesData[a, {b}, c]
];

(* ------------------------------------------------------------------------- *)
(* parameters of the model *)
nn          = 3;
As          = {{1,alp1,bet1},{bet2,1,alp2},{alp3,bet3,1}}
xs          = Table[Subscript[x,i],{i,nn}];
bs          = Table[Subscript[r,i],{i,nn}];
eps         = Table[Subscript[ep,i],{i,nn}];

(* drift and control vector field of the GLV model *)
Xx          =  xs * (bs - As . xs);
Yx          =  xs * eps;

(* collinearity colus *)
A11         = As[[2;;3,2;;3]];
e1          = Simplify/@Flatten[{0,Inverse[A11].eps[[2;;3]]}]
xe1         = Simplify/@Flatten[{0,Inverse[A11].bs[[2;;3]]}]
A22         = As[[{1,3}, {1,3}]];
aux         = Inverse[A22].eps[[{1,3}]];
e2          = Simplify/@Flatten[{aux[[1]],0,aux[[2]]}]
aux         = Inverse[A22].bs[[{1,3}]];
xe2         = Simplify/@Flatten[{aux[[1]],0,aux[[2]]}]
A33         = As[[{1,2}, {1,2}]];
e3          = Simplify/@Flatten[{Inverse[A33].eps[[1;;2]],0}]
xe3         = Simplify/@Flatten[{Inverse[A33].bs[[1;;2]],0}]
xe4          = FullSimplify/@(Inverse[As].bs)
e4          = FullSimplify/@(Inverse[As].eps)
(* four lines defining the collinearity locus *)
Ls          = {xe1 + t e1, xe2 + t e2, xe3 + t e3, xe4 + t e4};

(* determinantal varieties D, D' and D'' *)
Dx          = d12 xs[[1]] xs[[2]] +  d13 xs[[1]] xs[[3]] +  d23 xs[[2]] xs[[3]];
Dpx         = dp112 xs[[1]]^2 xs[[2]]+ dp122 xs[[1]] xs[[2]]^2 \
    + dp113 xs[[1]]^2 xs[[3]] + dp133 xs[[1]] xs[[3]]^2+ dp223 xs[[2]]^2 xs[[3]] \
    + dp233 xs[[2]] xs[[3]]^2 +dp123 xs[[1]] xs[[2]] xs[[3]] + dp12 xs[[1]] xs[[2]] \
    + dp13 xs[[1]] xs[[3]] + dp23 xs[[2]] xs[[3]];
Dppx        = dpp12 xs[[1]] xs[[2]] + dpp13 xs[[1]] xs[[3]] \
    + dpp23 xs[[2]] xs[[3]] + dpp1 xs[[1]] + dpp2 xs[[2]] + dpp3 xs[[3]];
<< "DDDs-exprs.m"

(* qaudric D''(x) = x.Qpp.x + 2 bpp.x *)
Qpp = 1/2 D[Dppx,{xs,2}];
bpp = 1/2 D[Dppx,{xs,1}] /. Thread[xs->0];

(* four lines defining the collinearity locus *)
Ls          = {xe1 + t e1, xe2 + t e2, xe3 + t e3};
eqs         = Simplify@((t+Dpx/Dx)/.Thread[xs->Simplify[#]]) & /@ Ls
aux         = Simplify/@(Solve[#==0,{t}] & /@ eqs)
(* abnormal equilibria *)
xes         = Flatten[Simplify/@(Ls[[#]] /. aux[[#]]) & /@ Table[i,{i,1,3}],1]

Xs          = Simplify/@(Xx -Dpx/Dx Yx);
aux         = Simplify/@(D[Xs,{xs,1}] /. Thread[xs->#] & /@ xes);

(* spectrum of the linearized singular dynamics at singular equilibria *)
(* eigenvalues*)
sp          = FullSimplify/@(Expand/@(Eigenvalues/@(aux)))
(* eigenvecteors*)
pv          = FullSimplify/@(Eigenvectors/@(aux))

Exit[]
