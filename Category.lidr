> module Category

> %default total

Basic definitions of category theory 
====================================

Define category, functor, natural transformation, adjoints, ...

Category
--------

> data Cat : Type where
>   MkCat : {- Objects -} 
>           (O:    Type) ->
>           {- Hom -}
>           (H:    O -> O -> Type) ->
>           {- Identities -}
>           (Id:   (a:O) -> H a a) ->
>           {- Composition -}
>           (Comp: {a:O} -> {b:O} -> {c:O} ->
>                  (f: H b c) -> (g: H a b) -> H a c) ->
>           {- Comp is associative -}
>           (Ass:  {a:O} -> {b:O} -> {c:O} -> {d:O} ->
>                  (f: H c d) -> (g : H b c) -> (h: H a b) ->
>                  (Comp (Comp f g) h) = (Comp f (Comp g h))) ->
>           {- Precomposing Id is the identity on Arrows -}
>           (IdPre: {a:O} -> {b:O} ->
>                  (f: H a b) -> (Comp f (Id a)) = f) ->
>           {- Postcomposing Id is the identity on Arrows -}
>           (IdPost: {a:O} -> {b:O} ->
>                  (f: H a b) -> (Comp (Id b) f) = f) ->
>           Cat

Getters for the components:
Obj and Hom take the category as an explicit argument

> Obj: Cat -> Type
> Obj  (MkCat O _ _ _ _ _ _) = O

> Hom: (cc:Cat) -> (a: Obj cc) -> (b: Obj cc) -> Type
> Hom  (MkCat _ H _ _ _ _ _ ) a b = H a b

the rest of the getters can have cc as an implicit argument...

> Id: {cc:Cat} -> (a: Obj cc) -> Hom cc a a
> Id  {cc=(MkCat _ _ id _ _ _ _)} a = id a

> Comp: {cc: Cat} -> {a:Obj cc} -> {b:Obj cc} -> {c:Obj cc} ->    
>       (f: Hom cc b c) -> (g: Hom cc a b) -> Hom cc a c
>
> Comp  {cc=(MkCat _ _ _ comp _ _ _)} f g = comp f g

> Ass:  {cc: Cat} -> {a:Obj cc} -> {b:Obj cc} -> 
>       {c:Obj cc} -> {d:Obj cc} ->
>       (f: Hom cc c d) -> (g : Hom cc b c) -> (h: Hom cc a b) ->
>       (Comp (Comp f g) h) = (Comp f (Comp g h))
>
> Ass   {cc=(MkCat _ _ _ _ ass _ _)} f g h = ass f g h

> IdPre: {cc: Cat} -> {a:Obj cc} -> {b:Obj cc} ->
>         (f: Hom cc a b) -> (Comp f (Id a)) = f
>
> IdPre  {cc=(MkCat _ _ _ _ _ idl _)} f = idl f

> IdPost: {cc: Cat} -> {a:Obj cc} -> {b:Obj cc} ->
>          (f: Hom cc a b) -> (Comp (Id b) f) = f
>
> IdPost  {cc=(MkCat _ _ _ _ _ _ idr)} f = idr f


Functor
-------

> data Fun : (cc: Cat) -> (dd: Cat) -> Type where
>   MkFun : {- Object map -}
>        (FO : Obj cc -> Obj dd) ->
>           {- Homomorphism map -}
>        (FH : {a: Obj cc} -> {b: Obj cc} ->
>              Hom cc a b -> Hom dd (FO a) (FO b)) ->
>           {- FH maps identities to identities -}
>        (FI : {a: Obj cc} -> (FH (Id a) = Id (FO a))) ->
>           {- FH commutes with composition -}
>        (FC : {a: Obj cc} -> {b: Obj cc} -> {c: Obj cc} ->
>              (f: Hom cc b c) -> (g: Hom cc a b) ->
>              (FH (Comp f g) = Comp (FH f) (FH g))) ->
>        Fun cc dd

and again the getters

> FunO : {cc: Cat} -> {dd: Cat} -> (Fun cc dd) ->
>        Obj cc -> Obj dd
> FunO (MkFun fo _ _ _) = fo

> FunH : {cc: Cat} -> {dd: Cat} -> {a: Obj cc} -> {b: Obj cc} ->
>        (ff : Fun cc dd) -> Hom cc a b -> 
>         Hom dd (FunO ff a) (FunO ff b)
> FunH (MkFun _ fh _ _) = fh

> FunId : {cc: Cat} -> {dd: Cat} -> {a: Obj cc} ->
>         (ff : Fun cc dd) -> (FunH ff (Id a) = Id (FunO ff a))
> FunId (MkFun _ _ fi _) = fi

> FunC : {cc: Cat} -> {dd: Cat} -> 
>        {a, b, c: Obj cc} ->
>        (ff : Fun cc dd) ->
>        (f: Hom cc b c) -> (g: Hom cc a b) ->
>        FunH ff (Comp f g) = Comp (FunH ff f) (FunH ff g)
> FunC (MkFun _ _ _ fc) = fc


Natural transformation
----------------------

> data NT : {cc: Cat} -> {dd: Cat} ->
>           (ff: Fun cc dd) -> (gg: Fun cc dd) -> Type where
>   MkNT : {- Component maps -}
>       (Cmp : (a: Obj cc) -> Hom dd (FunO ff a) (FunO gg a)) ->
>          {- Commutative squares -}
>       (CommSq : {a: Obj cc} -> {b: Obj cc} ->
>           (f: Hom cc a b) ->  -- type checker needs implicits...:
>           (Comp {b=FunO {cc} ff b} {c=FunO {cc} gg b} 
>             (Cmp b) (FunH {dd} ff f)) = 
>                     (Comp (FunH gg f) (Cmp a))) ->
>       NT ff gg

getters

> NTCmp : {cc: Cat} -> {dd: Cat} -> 
>         {ff: Fun cc dd} -> {gg: Fun cc dd} ->
>         NT ff gg -> (a: Obj cc) -> Hom dd (FunO ff a) (FunO gg a)
> NTCmp (MkNT cmp _) = cmp

> NTCommSq : {cc: Cat} -> {dd: Cat} ->
>         {ff: Fun cc dd} -> {gg: Fun cc dd} ->
>         {a: Obj cc} -> {b: Obj cc} -> 
>         (eta: NT ff gg) -> (f: Hom cc a b) ->
>         (Comp {b=FunO {cc} ff b} {c=FunO {cc} gg b} 
>             (NTCmp eta b) (FunH {dd} ff f)) = 
>                     (Comp (FunH gg f) (NTCmp eta a))
> NTCommSq (MkNT _ cs) = cs



