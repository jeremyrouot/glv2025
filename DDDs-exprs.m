nn          = 3;

(*
App         = D[Dppx,{xs,2}];
bpp         = {dpp1,dpp2,dpp3};
h           = Inverse[App].bpp;
(*Simplify@(Dppx - 1/2 (xs+h).A.(xs+h)+1/2 h.A.h)*)
P           = Orthogonalize[Transpose[Eigenvectors[App]]]
ys          = P.(xs+h) 
nDpp        = 1/2 ys.{lpp1,lpp2,lpp3}.ys - 1/2 h.App.h

As          = {{1,alp1,bet1},{bet2,1,alp2},{alp3,bet3,1}};
bs          = Table[Subscript[b,i],{i,nn}];
eps         = Table[Subscript[ep,i],{i,nn}];
*)

(*
normal = {alp1 -> (Subscript[ep, 1]^2 - Subscript[b, 2]*Subscript[ep, 1]^2 -
     Subscript[ep, 1]*Subscript[ep, 2] + Subscript[b, 1]*Subscript[ep, 1]*
      Subscript[ep, 2])/((Subscript[ep, 1] - Subscript[ep, 2])*
     Subscript[ep, 2]),
  bet1 -> (Subscript[ep, 1]^2 - Subscript[b, 3]*Subscript[ep, 1]^2 -
     Subscript[ep, 1]*Subscript[ep, 3] + Subscript[b, 1]*Subscript[ep, 1]*
      Subscript[ep, 3])/((Subscript[ep, 1] - Subscript[ep, 3])*
     Subscript[ep, 3]),
  alp2 -> (Subscript[ep, 2]^2 - Subscript[b, 3]*Subscript[ep, 2]^2 -
     Subscript[ep, 2]*Subscript[ep, 3] + Subscript[b, 2]*Subscript[ep, 2]*
      Subscript[ep, 3])/((Subscript[ep, 2] - Subscript[ep, 3])*
     Subscript[ep, 3]), bet2 -> (Subscript[ep, 1]*Subscript[ep, 2] -
     Subscript[b, 2]*Subscript[ep, 1]*Subscript[ep, 2] - Subscript[ep, 2]^2 +
     Subscript[b, 1]*Subscript[ep, 2]^2)/(Subscript[ep, 1]*
     (Subscript[ep, 1] - Subscript[ep, 2])),
  alp3 -> (Subscript[ep, 1]*Subscript[ep, 3] - Subscript[b, 3]*
      Subscript[ep, 1]*Subscript[ep, 3] - Subscript[ep, 3]^2 +
     Subscript[b, 1]*Subscript[ep, 3]^2)/(Subscript[ep, 1]*
     (Subscript[ep, 1] - Subscript[ep, 3])),
  bet3 -> (Subscript[ep, 2]*Subscript[ep, 3] - Subscript[b, 3]*
      Subscript[ep, 2]*Subscript[ep, 3] - Subscript[ep, 3]^2 +
     Subscript[b, 2]*Subscript[ep, 3]^2)/(Subscript[ep, 2]*
     (Subscript[ep, 2] - Subscript[ep, 3]))}

{alp1,alp2,alp3,bet1,bet2,bet3} = {alp1,alp2,alp3,bet1,bet2,bet3} /. normal
*)

vk1         = {alp3 eps[[2]]-bet2 eps[[3]], eps[[3]] -alp3 eps[[1]],bet2 eps[[1]] - eps[[2]]};
vk2         = {bet3 eps[[2]]- eps[[3]], alp1 eps[[3]] -bet3 eps[[1]],eps[[1]] - alp1 eps[[2]]};
vk3         = {eps[[2]]- alp2 eps[[3]], bet1 eps[[3]] - eps[[1]],alp2 eps[[1]] - bet1 eps[[2]]};
vk12        = {alp3 - bet2*bet3, -(alp1*alp3) + bet3, -1 + alp1*bet2};
vk13        = {alp2*alp3 - bet2, 1 - alp3*bet1, -alp2 + bet1*bet2};
vk23        = {-1 + alp2*bet3, alp1 - bet1*bet3, -(alp1*alp2) + bet1};

d12         = eps[[1]] (eps[[1]]-eps[[2]]) eps[[2]] vk12.eps;
d13         = eps[[1]] (eps[[1]]-eps[[3]]) eps[[3]] vk13.eps;
d23         = eps[[2]] (eps[[2]]-eps[[3]]) eps[[3]] vk23.eps;
(*Dx        = Times@@xs (d12 xs[[1]] xs[[2]] +  d13 xs[[1]] xs[[3]] +  d23 xs[[2]] xs[[3]]);*)

dp12        = (bs[[1]] - bs[[2]]) eps[[1]] eps[[2]] vk12.eps;
dp13        = (bs[[1]] - bs[[3]]) eps[[1]] eps[[3]] vk13.eps;
dp23        = (bs[[2]] - bs[[3]]) eps[[2]] eps[[3]] vk23.eps;
dp112       = -vk12.eps (eps[[1]]-eps[[2]]) bet2 eps[[1]]; 
dp122       = -vk12.eps (eps[[1]]-eps[[2]]) alp1 eps[[2]]; 
dp113       = -vk13.eps (eps[[1]]-eps[[3]]) alp3 eps[[1]];
dp133       = -vk13.eps (eps[[1]]-eps[[3]]) bet1 eps[[3]]; 
dp223       = -vk23.eps (eps[[2]]-eps[[3]]) bet3 eps[[2]];
dp233       = -vk23.eps (eps[[2]]-eps[[3]]) alp2 eps[[3]]; 
dp123       = -eps[[2]] (eps[[1]]-eps[[3]]) (alp3 vk23 + bet1 vk12).eps+ eps[[1]] (eps[[2]]-eps[[3]]) (alp2 vk12- bet3 vk13).eps + eps[[3]] (eps[[1]]-eps[[2]]) (bet2 vk23- alp1 vk13).eps;

(*Dpx       = Times@@xs (dp112 xs[[1]]^2 xs[[2]]+ dp122 xs[[1]] xs[[2]]^2 + dp113 xs[[1]]^2 xs[[3]] + dp133 xs[[1]] xs[[3]]^2+ dp223 xs[[2]]^2 xs[[3]] + dp233 xs[[2]] xs[[3]]^2 +dp123 xs[[1]] xs[[2]] xs[[3]] + dp12 xs[[1]] xs[[2]] + dp13 xs[[1]] xs[[3]] + dp23 xs[[2]] xs[[3]]);*)

dpp1        = eps[[1]] vk1.bs;
dpp2        = eps[[2]] vk2.bs;
dpp3        = eps[[3]] vk3.bs;
dpp12       = vk12.eps (eps[[1]]-eps[[2]]);
dpp13       = vk13.eps (eps[[1]]-eps[[3]]);
dpp23       = vk23.eps (eps[[2]]-eps[[3]]);




(*
e4=Inverse[As].eps
e23=e4[[1]]
e13=e4[[2]]
e12=e4[[3]]
f4=Inverse[As].bs
f23=f4[[1]]
f13=f4[[2]]
f12=f4[[3]]

FullSimplify@Expand@(d23 e12 e13)
FullSimplify@Expand@(dp23 e12 e13) 
FullSimplify@Expand@(dp13 e12 e23 + dp12 e13 e23) 
FullSimplify@Expand@(dp12 e13 e23) 
FullSimplify@Expand@(d23 e13 f12)
*)
