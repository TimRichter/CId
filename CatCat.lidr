> module CatCat
> import Category
> import Prop
> import FunExtAxiom
> import Syntax.PreorderReasoning


> %default total
> %auto_implicits off
> %access public export

Category of (small) categories and functors as morphisms
--------------------------------------------------------

All our categories are small in the sense that they have 
types as objects and as homs.

1) Functor composition yields a functor

it preserves identities:

> fid : {cc, dd, ee : Cat} ->
>       (ff : Func dd ee) -> (gg : Func cc dd) -> 
>       (c : Obj cc) -> 
>       ((FH {a = (FO gg c)} {b = (FO gg c)} ff) . (FH gg)) (Id c) = 
>         Id (((FO ff).(FO gg)) c)
>
> fid {cc} {dd} {ee} ff gg c =
>   (((FH {a = (FO gg c)} {b = (FO gg c)} ff) . (FH gg)) (Id c))
>   ={ cong {f = \m => (FH {a = (FO gg c)} {b = (FO gg c)} ff) m} 
>       (FId gg c) }=
>   ((FH {a = (FO gg c)} {b = (FO gg c)} ff) (Id (FO gg c)))
>   ={ FId {cc = dd} ff (FO gg c) }=
>   (Id (((FO ff) . (FO gg)) c))
>   QED

and composition:

> comp :  {cc, dd, ee : Cat} -> (ff : Func dd ee) -> (gg : Func cc dd) -> 
>         {a, b, c: Obj cc} -> (f : Hom cc b c) -> (g : Hom cc a b) ->
>         (FH ff (FH gg (Comp f g)))
>             = Comp (FH ff (FH gg f)) (FH ff (FH gg g))
> comp ff gg {a} {b} {c} f g = 
>   (FH ff (FH gg (Comp f g)))
>   ={ cong {f = \x => FH ff x} (FC {a} {b} {c} gg f g) }=
>   (FH ff (Comp (FH gg f) (FH gg g)))
>   ={ FC {a = FO gg a} {b = FO gg b} {c = FO gg c}
>       ff (FH gg f) (FH gg g) }=
>   (Comp (FH ff (FH gg f)) (FH ff (FH gg g)))
>   QED

so we can define

> funComp : {cc, dd, ee : Cat} ->
>           (ff : Func dd ee) -> (gg : Func cc dd) -> Func cc ee
> funComp ff gg =  MkFunc  ((FO ff) . (FO gg))
>                         ((FH ff) . (FH gg))
>                         (fid ff gg)
>                         (comp ff gg)

2) functor composition is associative

to show equality of two functors, it is enough to show equality of the
object and morphism maps:

First we have to show that given equal object and morphism maps, 
the types that FId's and FC's are equalities in are equal

> funEqI :  {cc, dd: Cat} -> 
>           (fO, gO : Obj cc -> Obj dd) -> 
>           (eqO : fO = gO) ->
>           -- FId ff is equality in Hom dd (FO ff a) (FO ff a)
>           -- FId gg is equality in Hom dd (FO gg a) (FO gg a)  for some a : Obj cc
>           ({a: Obj cc} -> Hom dd (fO a) (fO a)) = 
>           ({a: Obj cc} -> Hom dd (gO a) (gO a))
> funEqI {cc} {dd} fO gO eqO =
>       ({a: Obj cc} -> Hom dd (fO a) (fO a))
>       ={ cong {f = \oMap => ({a: Obj cc} -> Hom dd (oMap a) (oMap a) )} eqO }=
>       ({a: Obj cc} -> Hom dd (gO a) (gO a))
>       QED

> funEqC :  {cc, dd: Cat} -> 
>           (fO, gO: Obj cc -> Obj dd) -> 
>           (eqO : fO = gO) ->
>           -- FC ff is equality in Hom dd (FO ff a) (FO ff c)
>           -- FC gg is equality in Hom dd (FO gg a) (FO gg c)  for some a, c : Obj cc
>           ({a, c: Obj cc} -> Hom dd (fO a) (fO c)) = 
>           ({a, c: Obj cc} -> Hom dd (gO a) (gO c))
> funEqC {cc} {dd} fO gO eqO =
>       ({a, c : Obj cc} -> Hom dd (fO a) (fO c))
>       ={ cong {f = \oMap => ({a, c: Obj cc} -> Hom dd (oMap a) (oMap c) )} eqO }=
>       ({a, c : Obj cc} -> Hom dd (gO a) (gO c))
>       QED

funEqI and funEqC are very similar, do we really need both?

Here is yet another variant. Only difference: explicit object argument in the types
that are proved equal

> funEqI2 : {cc, dd: Cat}  -> 
>           (fO, gO : Obj cc -> Obj dd) -> 
>           (eqO : fO = gO) ->
>           -- FId ff is equality in Hom dd (FO ff a) (FO ff a)
>           -- FId gg is equality in Hom dd (FO gg a) (FO gg a)  for some a : Obj cc
>           ((a: Obj cc) -> (Hom dd (fO a) (fO a))) = 
>           ((a: Obj cc) -> (Hom dd (gO a) (gO a)))
> funEqI2 {cc} {dd} fO gO eqO =
>       ((a: Obj cc) -> Hom dd (fO a) (fO a))
>       ={ cong {f = \oMap => ((a: Obj cc) -> Hom dd (oMap a) (oMap a) )} eqO }=
>       ((a: Obj cc) -> Hom dd (gO a) (gO a))
>       QED

< funEqP0 : {cc, dd: Cat} -> (ff, gg: Func cc dd) ->
<         (eqO : (FO ff) = (FO gg)) -> 
<         (eqH : (FH ff) = (FH gg)) ->        
<         (a : Obj cc) -> FId ff a = FId gg a
< funEqP0 {cc} {dd} (MkFunc fO fH fI fC) (MkFunc gO gH gI gC) eqO eqH a = 
<     (FId (MkFunc fO fH fI fC) a)  ={ Refl }=
<     (fI a)                       


?lala where

>           -- types: goal: fI a = gI a
>           --        (fI a) : fH (Id a) = Id (fO a)
>           --        (gI a) : gH (Id a) = Id (gO a)
>           --    i.e. suffices
>           --           IsPropH (fH (Id a) = Id (fO a)) (gH (Id a) = Id (gO a))
>           --        fH (Id a) : Hom dd (fO a) (fO a)
>           --        gH (Id a) : Hom dd (gO a) (gO a)

         UipWTH2 teq1 teq1 eq1 eq2 (fI a) (gI a) where

           eqOa : (fO a) = (gO a)
           eqOa = ?lulu


cong {f = \fObj => fObj a} eqO


           -- teq1 : (Hom dd (fO a) (fO a))  =  (Hom dd (gO a) (gO a))
           teq1 = cong {f = \obj => Hom dd obj obj} eqOa 
           -- eq1 : (fH (Id a)) = (gH (Id a))
           eq1 = cong {f = \fHom => fHom (Id a)} eqH
           -- eq2 : (Id (fO a)) = (Id (gO a))
           eq2 = cong {f = Id} eqOa

< funEqP1 : {cc, dd: Cat} -> (ff, gg: Func cc dd) ->
<         (eqO : (FO ff) = (FO gg)) -> 
<         (eqH : (FH ff) = (FH gg)) ->        
<         FId ff = FId gg           -- FId ff : (a : Obj cc) -> (fH (Id a)) = Id (fO a)
< funEqP1 {cc} {dd} ff gg eqO eqH = 
<   funextD {A = Obj cc} 
<     {B1 = (\a => ((=) 
<             {A = Hom dd (FO ff a) (FO ff a)} 
<             {B = Hom dd (FO ff a) (FO ff a)} 
<             (FH ff (Id a)) (Id (FO a))))} 
<     {B2 = (\a => ((=)
<             {A = Hom dd (FO gg a) (FO gg a)} 
<             {B = Hom dd (FO gg a) (FO gg a)} 
<             (FH ff (Id a)) (Id (FO gg a))))} 
<     (FId ff) (FId gg) (prf {cc = cc} {dd = dd} ff gg eqO eqH)
<     where
<       prf : {cc, dd: Cat} -> (ff, gg : Func cc dd) ->
<             (eqO : (FO ff) = (FO gg)) -> 
<             (eqH : (FH ff) = (FH gg)) ->        
<             (w : Obj cc) -> (FId ff w) = (FId gg w)
<       prf = ?lala

where
       prf = ?lala

<       prf : (a: Obj cc) -> fI a = gI a
<       prf a = ?lala


UipWTH  {teq = ?three} ?one ?two (fI a) (gI a)

funEqI2 {cc} {dd} {a} fO gO eqO
(cong {f = \hh => hh a a (Id a)} eqH) 
           (cong {f = \oo => Id (oo a)} eqO) fI gI


< funEq : {cc, dd: Cat} -> (ff, gg: Func cc dd) ->
<         (eqO : (FO ff) = (FO gg)) -> 
<         (eqH : (FH ff) = (FH gg)) ->
<         ff = gg

< funEq {cc} {dd} (MkFunc fO fH fI fC) (MkFunc gO gH gI gC) eqO eqH =
<   (MkFunc fO fH fI fC)   ={ cong {f = \o => MkFunc o fH fI fC} eqO }=
<   (MkFunc gO fH fI fC)   ={ cong {f = \h => MkFunc gO h fI fC} eqH }=
<   (MkFunc gO gH fI fC)   ={ cong {f = \i => MkFunc gO gH i fC} (UipWT {teq = funEqI fO gO eqO } fI gI) }=
<   (MkFunc gO gH gI fC)   ={ cong {f = \c => MkFunc gO gH gI c} (UipWT {teq = funEqC fO gO eqO } fC gC) }=
<   (MkFunc gO gH gI gC)   QED

< funCompAssociative : {aa, bb, cc, dd : Cat} ->  
<   (ff : Func cc dd) -> (gg : Func bb cc) -> (hh : Func aa bb) ->
<   funComp (funComp ff gg) hh = funComp ff (funComp gg hh)
< funCompAssociative {aa} {bb} {cc} {dd} ff gg hh = 
<   (MkFunc lO lH lI lC)  ={ ?lele {-cong Refl-} }=
<   (MkFunc rO lH lI lC)  ={ ?lulu {-cong Refl-} }=
<   (MkFunc rO rH lI lC)  ={ ?lala {-cong (Uip lI rI)-} }=
<   (MkFunc rO rH rI lC)  ={ ?lulu {-cong (Uip lC rC)-} }=
<   (MkFunc rO rH rI rC)  ={ Refl }=
<   (rhs)                QED  
<   where
<     lhs = funComp (funComp ff gg) hh
<     rhs = funComp ff (funComp gg hh) 
<     lO  = FO lhs
<     lH  = FH lhs
<     lI  = FId lhs
<     lC  = FC lhs  
<     rO  = FO rhs
<     rH  = FH rhs
<     rI  = FId rhs
<     rC  = FC rhs  



