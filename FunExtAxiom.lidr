> module FunExtAxiom

> %default total

If needed, we'll add function extensionality as an axiom

> funext : {A, B : Type} -> (f: A -> B) -> (g: A -> B) ->
>          ((a : A) -> (f a) = (g a)) -> (f = g)
> funext f g h = really_believe_me h

> funextD : {A : Type} -> {B1 : A -> Type} -> {B2 : A -> Type} ->
>           (f: (x : A) -> (B1 x)) -> (g: (x : A) -> (B2 x)) ->
>           ((a : A) -> ((f a) = (g a))) -> (f = g)
> funextD f g h = really_believe_me h
