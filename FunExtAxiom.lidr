> module FunExtAxiom

> %default total
> %auto_implicits off
> %access public export

If needed, we'll add function extensionality as an axiom

> funext :    {A, B : Type} -> 
>             (f: A -> B) -> 
>             (g: A -> B) ->
>             ((a : A) -> (f a) = (g a)) -> 
>             f = g
> funext f g h = really_believe_me h

> funextD :   {A : Type} -> 
>             {B1 : A -> Type} -> 
>             {B2 : A -> Type} ->
>             (f: (x : A) -> (B1 x)) -> 
>             (g: (x : A) -> (B2 x)) ->
>             ((a : A) -> ((f a) = (g a))) -> 
>             f = g
> funextD f g h = really_believe_me h

> funextD2 :  {A : Type} -> 
>             {B : A -> Type} ->
>             {C1 : (x : A) -> B x -> Type} ->
>             {C2 : (x : A) -> B x -> Type} ->
>             (f : (x : A) -> (y : B x) -> C1 x y) ->
>             (g : (x : A) -> (y : B x) -> C2 x y) ->
>             ((x : A) -> (y : B x) ->  f x y = g x y) ->
>             f = g
> funextD2 f g h = really_believe_me h


