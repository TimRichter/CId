> module FunCat
> import Category
> import FunExtAxiom
> import Syntax.PreorderReasoning

> %default total

Given two (small) categories cc and dd, we
have the category of functors Funs cc dd

identity natural transformation:

> idNT :  (ff : Fun cc dd) -> NT ff ff
> idNT {cc} {dd} ff = MkNT cmpId commSqId where
>
>   cmpId : (a : Obj cc) -> Hom dd (FO ff a) (FO ff a)
>   cmpId a = Id (FO ff a)
>
>   commSqId :  (f : Hom cc a b) ->               
>               ((cmpId b) ° (FH ff f)) = ((FH ff f) ° (cmpId a))
>   commSqId {a} {b} f =
>     ((cmpId b) ° (FH ff f))       ={ Refl }=
>     ((Id (FO ff b)) ° (FH ff f))  ={ IdPost (FH ff f) }=
>     (FH ff f)                     ={ sym (IdPre (FH ff f)) }=
>     ((FH ff f) ° (Id (FO ff a)))  ={ Refl }=
>     ((FH ff f) ° (cmpId a))       QED

composition of natural transformations:

component maps are composed in dd:

> cmpST : {cc, dd : Cat} -> {ff, gg, hh : Fun cc dd} ->
>         (s : NT gg hh) -> (t : NT ff gg) ->
>         (a : Obj cc) -> Hom dd (FO ff a) (FO hh a)
> cmpST s t a = (s _ a) ° (t _ a)

squares commute since they are put together from the commtative squares
of the transformations being composed

> commSqST :  {cc, dd : Cat} -> {ff, gg, hh : Fun cc dd} ->
>         (s : NT gg hh) -> (t : NT ff gg) ->
>         {a, b : Obj cc} -> (f : Hom cc a b) ->               
>         ((cmpST s t b) ° (FH ff f)) = ((FH hh f) ° (cmpST s t a))
> commSqST {ff} {gg} {hh} s t {a} {b} f = 
>   ((cmpST s t b) ° (FH ff f))        ={ Refl }=
>   (((s _ b) ° (t _ b)) ° (FH ff f))  ={ Ass (s _ b) (t _ b) (FH ff f) }=
>   ((s _ b) ° ((t _ b) ° (FH ff f)))  ={ cong {f = \x => ((s _ b) ° x)} (NTSq t f) }=
>   ((s _ b) ° ((FH gg f) ° (t _ a)))  ={ sym (Ass (s _ b) (FH gg f) (t _ a)) }=      
>   (((s _ b) ° (FH gg f)) ° (t _ a) ) ={ cong {f = \x => x ° (t _ a)} (NTSq s f) }=
>   (((FH hh f) ° (s _ a)) ° (t _ a))  ={ Ass (FH hh f) (s _ a) (t _ a) }=
>   ((FH hh f) ° ((s _ a) ° (t _ a)))  ={ Refl }=
>   ((FH hh f) ° (cmpST s t a))        QED    

> compNT :  {cc, dd : Cat} -> {ff, gg, hh : Fun cc dd} ->
>           NT gg hh -> NT ff gg -> NT ff hh
> compNT s t = MkNT (cmpST s t) (commSqST s t) 

associativity of compNT

> assLemma1 : {cc, dd : Cat} -> {ff,gg,hh,kk: Fun cc dd} ->
>       (t : NT hh kk) -> (r : NT gg hh) -> (s : NT ff gg) ->
>       (a : Obj cc) -> 
>       NTC (compNT (compNT t r) s) a = NTC (compNT t (compNT r s)) a 

> assLemma1 t r s a = 
>     (NTC (compNT (compNT t r) s) a)   ={ Refl }=
>     (((t _ a) ° (r _ a)) ° (s _ a))   ={ Ass (t _ a) (r _ a) (s _ a) }=
>     ((t _ a) ° ((r _ a) ° (s _ a)))   ={ Refl }=
>     (NTC (compNT t (compNT r s)) a)   QED

> assLemma2 : {cc, dd : Cat} -> {ff,gg,hh,kk: Fun cc dd} ->
>       (t : NT hh kk) -> (r : NT gg hh) -> (s : NT ff gg) ->
>       NTC (compNT (compNT t r) s) = NTC (compNT t (compNT r s))
> assLemma2 t r s = funext (NTC (compNT (compNT t r) s)) 
>                          (NTC (compNT t (compNT r s)))
>                          (assLemma1 t r s)


> FunCat : (cc, dd : Cat) -> Cat
> FunCat cc dd = MkCat
>   (Fun cc dd) (NT {cc} {dd}) idNT compNT ?ass1 ?idPre ?idPost 

