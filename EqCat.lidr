> module EqCat
> import Category
> import Prop
> %default total

Each Idris type A forms a category where the class of
objects is A and Hom x y = (x = y)

Associativity and the properties of identity (Refl) are
easily proved using Uip:

> ass : {A : Type} -> {a,b,c,d : A} -> 
>       (p: c = d) -> (q : b = c) -> (r : a = b) ->
>       (trans r (trans q p)) = (trans (trans r q) p)
> ass p q r = Uip (trans r (trans q p)) (trans (trans r q) p)

> idPre : {A : Type} -> {a, b : A} -> (p : a = b) -> (trans Refl p) = p
> idPre p = Uip (trans Refl p) p

> idPost : {A : Type} -> {a, b : A} -> (p : a = b) -> (trans p Refl) = p
> idPost p = Uip (trans p Refl) p

> eqCat : (A : Type) -> Cat
> eqCat A = MkCat A 
>                 ((=) {A=A} {B=A}) 
>                 (\x => Refl) 
>                 (flip (trans {x=A} {y=A} {z=A})) 
>                 ass 
>                 idPre  
>                 idPost

These are of course groupoids.
TODO: define groupoids and prove this.

And since we have Uip, these are all discrete. 
TODO: define "discrete" and prove this.

