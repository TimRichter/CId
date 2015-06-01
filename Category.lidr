> module Category

> %default total

Basic definitions of category theory 
====================================

Define category, functor, natural transformation

Category
--------

> data Cat : Type where
>   MkCat : {- Objects -} 
>           (O :      Type) ->
>           {- Hom -}
>           (H :      O -> O -> Type) ->
>           {- Identities -}
>           (Id :     (a : O) -> H a a) ->
>           {- Composition -}
>           (Comp :   {a, b, c : O} ->
>                     (f : H b c) -> (g : H a b) -> H a c) ->
>           {- Comp is associative -}
>           (Ass :    {a, b, c, d : O} ->
>                     (f: H c d) -> (g : H b c) -> (h : H a b) ->
>                     (Comp (Comp f g) h) = (Comp f (Comp g h))) ->
>           {- Precomposing Id is the identity on Arrows -}
>           (IdPre :  {a, b : O} -> (f : H a b) -> 
>                     (Comp f (Id a)) = f) ->
>           {- Postcomposing Id is the identity on Arrows -}
>           (IdPost : {a, b : O} -> (f : H a b) -> 
>                  (Comp (Id b) f) = f) ->
>           Cat

Getters for the components:
Obj and Hom take the category as an explicit argument

> Obj : Cat -> Type
> Obj   (MkCat O _ _ _ _ _ _) = O

> Hom : (cc : Cat) -> (a, b : Obj cc) -> Type
> Hom   (MkCat _ H _ _ _ _ _ ) a b = H a b

the rest of the getters can have cc as an implicit argument...

> Id :  {cc : Cat} -> (a : Obj cc) -> Hom cc a a
> Id    {cc=(MkCat _ _ id _ _ _ _)} a = id a

> Comp :  {cc : Cat} -> {a, b, c : Obj cc} ->    
>         (f : Hom cc b c) -> (g : Hom cc a b) -> Hom cc a c
>
> Comp  {cc=(MkCat _ _ _ comp _ _ _)} f g = comp f g

> Ass : {cc : Cat} -> {a, b, c, d : Obj cc} ->
>       (f : Hom cc c d) -> (g : Hom cc b c) -> (h : Hom cc a b) ->
>       (Comp (Comp f g) h) = (Comp f (Comp g h))
>
> Ass   {cc=(MkCat _ _ _ _ ass _ _)} f g h = ass f g h

> IdPre : {cc : Cat} -> {a, b : Obj cc} ->
>         (f: Hom cc a b) -> (Comp f (Id a)) = f
>
> IdPre {cc=(MkCat _ _ _ _ _ idl _)} f = idl f

> IdPost :  {cc: Cat} -> {a, b : Obj cc} ->
>           (f: Hom cc a b) -> (Comp (Id b) f) = f
>
> IdPost  {cc=(MkCat _ _ _ _ _ _ idr)} f = idr f

> syntax [f] "°" [g] = Comp f g

Functor
-------

> data Fun : (cc : Cat) -> (dd : Cat) -> Type where
>   MkFun : {- Object map -}
>        (FO : Obj cc -> Obj dd) ->
>           {- Homomorphism map -}
>        (FH : {a, b : Obj cc} ->
>              Hom cc a b -> Hom dd (FO a) (FO b)) ->
>           {- FH maps identities to identities -}
>        (FI : (a : Obj cc) -> (FH (Id a) = Id (FO a))) ->
>           {- FH commutes with composition -}
>        (FC : {a, b, c: Obj cc} ->
>              (f : Hom cc b c) -> (g : Hom cc a b) ->
>              (FH (f ° g) = (FH f) ° (FH g))) ->
>        Fun cc dd

getters

> FO :  {cc, dd : Cat} -> (Fun cc dd) ->
>         Obj cc -> Obj dd
> FO  (MkFun fo _ _ _) = fo

> FH :  {cc, dd : Cat} -> {a, b : Obj cc} ->
>         (ff : Fun cc dd) -> Hom cc a b -> 
>         Hom dd (FO ff a) (FO ff b)
> FH (MkFun _ fh _ _) = fh

> FId : {cc, dd : Cat} -> (ff : Fun cc dd) -> 
>       (a : Obj cc) -> (FH ff (Id a) = Id (FO ff a))
> FId (MkFun _ _ fi _) = fi

> FC :  {cc, dd : Cat} -> 
>       {a, b, c : Obj cc} ->
>       (ff : Fun cc dd) ->
>       (f : Hom cc b c) -> (g : Hom cc a b) ->
>       FH ff (f ° g) = (FH ff f) ° (FH ff g)
> FC  (MkFun _ _ _ fc) = fc


Natural transformation
----------------------

> data NT : {cc, dd : Cat} ->
>           (ff, gg : Fun cc dd) -> Type where
>   MkNT : {- Component maps -}
>       (Cmp : (a: Obj cc) -> Hom dd (FO ff a) (FO gg a)) ->
>          {- Commutative squares -}
>       (CommSq : {a, b : Obj cc} ->
>           (f : Hom cc a b) ->  
>           {- type checker needs the implicits... -}
>           (Comp {b = FO {cc} ff b} {c = FO {cc} gg b} 
>             (Cmp b) (FH {dd} ff f)) = 
>                     ((FH gg f) ° (Cmp a))) ->
>       NT ff gg

getters

> NTC : {cc, dd : Cat} -> {ff, gg : Fun cc dd} ->
>         NT ff gg -> (a: Obj cc) -> Hom dd (FO ff a) (FO gg a)
> NTC (MkNT cmp _) = cmp

> NTSq :  {cc, dd : Cat} -> {ff, gg : Fun cc dd} -> 
>         {a, b : Obj cc} -> 
>         (eta : NT ff gg) -> (f : Hom cc a b) ->
>         ((NTC eta b) ° (FH {dd} ff f)) = 
>         ((FH gg f) ° (NTC eta a))
> NTSq (MkNT _ cs) = cs

> syntax [s] "_" [a] = (NTC s) a


