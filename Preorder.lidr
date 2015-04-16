> module Preorder
> import Prop

> %default total

Preorders, partial orders, linear orders
========================================

Relations
---------

A binary relation between types X and Y is a "subset" of the cartesian 
product XxY



Preorder
--------

To model a preordered set ("quasigeordnete Menge" in the
lecture):

> data Preorder : Type where
>   MkPreorder :  {- the set is modeled as a type -}
>                 (O: Type) ->
>                 {- the fact "a R b" is also modeled by a type -}
>                 (R: O -> O -> Type) ->
>                 {- R is reflexive -}
>                 (Ref: (a:O) -> R a a) ->
>                 {- R is transitive -}
>                 (Trans: {a:O} -> {b:O} -> {c:O} ->
>                          R b c -> R a b -> R a c) ->
>                 {- the types "a R b" have at most one inhabitant,
>                    i.e. they are "Propositions" -}
>                 (IsPropR: {a:O} -> {b:O} -> IsProp (R a b)) ->
>                 Preorder




