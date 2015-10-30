> module SigmaIsos

> import Control.Isomorphism
>
> %default total

> wrapSigma : {A : Type} -> {B : A -> Type} -> {C : Type} ->
>             ((a : A) -> (b : B a) -> C) ->
>             ((w : (a : A ** B a)) -> C)
> wrapSigma f (a ** b) = f a b

> wrapSigmaD : {A : Type} -> {B : A -> Type} -> 
>              {CF : ((a : A) -> (b : B a) -> Type)} -> 
>              ((a : A) -> (b : B a) -> (CF a b)) -> 
>              ((w : (a : A ** B a)) -> (wrapSigma CF) w)
> wrapSigmaD f (a ** b) = f a b


> unWrapSigma : {A : Type} -> {B : A -> Type} -> {C : Type} ->
>             ((w : (a : A ** B a)) -> C) ->
>             ((a : A) -> (b : B a) -> C)
> unWrapSigma f a b = f (a ** b)

> unWrapSigmaD : {A : Type} -> {B : A -> Type} -> 
>              {CF : ((a : A ** B a) -> Type)} -> 
>              ((w : (a : A ** B a)) -> CF w) ->
>              ((a : A) -> (b : B a) -> (unWrapSigma CF) a b)
> unWrapSigmaD f a b = f (a ** b)


