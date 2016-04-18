> module DependentCurrying

> import Control.Isomorphism
>
> %default total
> %auto_implicits off
> %access public export

> uncurrySigma : 
>             {A : Type} -> {B : A -> Type} -> {C : Type} ->
>             ({a : A} -> (b : B a) -> C) ->
>             ((w : (a : A ** B a)) -> C)
>
> uncurrySigma f (a ** b) = f b

> uncurrySigmaD : 
>             {A : Type} -> {B : A -> Type} -> 
>             {C : ({a : A} -> (b : B a) -> Type)} -> 
>             ({a : A} -> (b : B a) -> C b) -> 
>             ( (w : (a : A ** B a)) -> 
>               uncurrySigma {A} {B} {C=Type} C w
>             )
>
> uncurrySigmaD f (a ** b) = f b


> depPr : {A : Type} -> {B : A -> Type} ->
>         {a : A} -> (b : B a) -> A
> depPr {a} b = a


> currySigma : 
>             {A : Type} -> {B : A -> Type} -> {C : Type} ->
>             ((w : (a : A ** B a)) -> C) ->
>             ({a : A} -> (b : B a) -> C)
>
> currySigma f b = f ((depPr b) ** b)

> currySigmaD : 
>             {A : Type} -> {B : A -> Type} -> 
>             {C : ((a : A ** B a) -> Type)} -> 
>             ((w : (a : A ** B a)) -> C w) ->
>             ({a : A} -> (b : B a) -> (currySigma C) b)
> currySigmaD f b = f ((depPr b) ** b)


