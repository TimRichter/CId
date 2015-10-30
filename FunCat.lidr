> module FunCat
> import Category
> import FunExtAxiom
> import Prop
> import Syntax.PreorderReasoning

> %default total

Given two (small) categories cc and dd, we
have the category of functors Funs cc dd

identity natural transformation:

> idNT :  (ff : Fun cc dd) -> NT ff ff
> idNT {cc} {dd} ff = MkNT  (cmpId ff) 
>                           (commSqId ff) where
>
>   cmpId : (ff: Fun cc dd) -> 
>           (a : Obj cc) -> Hom dd (FO ff a) (FO ff a)
>   cmpId ff a = Category.Id (FO ff a)
>
>   commSqId :  (ff: Fun cc dd) -> {a, b : Obj cc} -> (f : Hom cc a b) ->               
>               ((cmpId ff b) ° (FH ff f)) = ((FH ff f) ° (cmpId ff a))
>   commSqId ff {a} {b} f =
>     ((cmpId ff b) ° (FH ff f))    ={ Refl }=
>     ((Id (FO ff b)) ° (FH ff f))  ={ IdPost (FH ff f) }=
>     (FH ff f)                     ={ sym (IdPre (FH ff f)) }=
>     ((FH ff f) ° (Id (FO ff a)))  ={ Refl }=
>     ((FH ff f) ° (cmpId ff a))    QED

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

first the components

> assCLemma : {cc, dd : Cat} -> 
>             {ff, gg, hh, kk: Fun cc dd} ->
>             (t : NT hh kk) -> 
>             (r : NT gg hh) -> 
>             (s : NT ff gg) ->
>             NTC (compNT (compNT t r) s) = NTC (compNT t (compNT r s))
> assCLemma {cc} {dd} {ff} {gg} {hh} {kk} t r s = 
>     funextD {A = Obj cc} 
>             {B1 = \a => Hom dd (FO ff a) (FO kk a)}
>             {B2 = \a => Hom dd (FO ff a) (FO kk a)} 
>             (NTC (compNT (compNT t r) s))
>             (NTC (compNT t (compNT r s)))
>             (\a => Ass (t _ a) (r _ a) (s _ a))

then the squares

> assSqLemma : {cc, dd : Cat} -> 
>             {ff, gg, hh, kk: Fun cc dd} ->
>             (t : NT hh kk) -> 
>             (r : NT gg hh) -> 
>             (s : NT ff gg) ->
>             NTSq (compNT (compNT t r) s) = NTSq (compNT t (compNT r s))
> assSqLemma {cc} {dd} {ff} {gg} {hh} {kk} t r s =  
>     funextD {A = Hom cc a b}
>             
>             (NTSq (compNT (compNT t r) s))
>             (NTSq (compNT t (compNT r s)))
>             (\f => Uip ())




> FunCat : (cc, dd : Cat) -> Cat
> FunCat cc dd = MkCat
>   (Fun cc dd) (NT {cc} {dd}) (idNT {cc} {dd}) (compNT {cc} {dd}) ?ass ?idPre ?idPost 



