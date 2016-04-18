> module Signatures
> import Data.Vect

> %default total

A signature is just a type family over |Nat|,
the n-ary symbols in Signature |sig| being
the elements of type |sig n|

> Sig : Type
> Sig = Nat -> Type

Now we build the family of n-ary Terms over 
a signature

terms will be a treelike type over Baseterms:

> data Term : (s : Sig) -> Nat -> Type where
>   Pr    : {s : Sig} -> {n : Nat} -> 
>           (i: Nat) -> {auto smaller: i `LT` n} -> Term s n
>   (:::) : {s : Sig} -> {m, n : Nat} -> s m -> Vect m (Term s n) -> Term s n








