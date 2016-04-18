> module TypeCat
> import Category

> %default total
> %auto_implicits off
> %access public export

Idris types with functions form a category
------------------------------------------

Preparations:
 
function composition is associative

> funCompAss : {A, B, C, D : Type} ->
>              (f : C -> D) -> (g : B -> C) -> (h : A -> B) ->
>              (f . (g . h)) = ((f . g) . h)
> funCompAss f g h = Refl


> idPre : {A, B : Type} -> (f : A -> B) -> 
>         (f . Prelude.Basics.id) = f
> idPre f = Refl

> idPost : {A, B : Type} -> (f : A -> B) -> 
>         ((Prelude.Basics.id {a = B}). f) = f
> idPost f = Refl

Can't write (->) ... why?

> Maps : Type -> Type -> Type
> Maps A B = A -> B

identity function with an explicit type argument

> idExpl : (a : Type) -> (a -> a)
> idExpl a = id

> TypeCat : Cat
> TypeCat = MkCat Type Maps idExpl (.) funCompAss idPre idPost

