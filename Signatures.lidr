> module Signatures
> import Data.Vect

> %default total

A signature is just a type family over |Nat|,
the n-ary symbols in Signature |MkSig sig| being
the elements of type |sig n|

> Sig : Type
> Sig = Nat -> Type

Now we build the family of n-ary Terms over 
a signature

terms will be a treelike type over Baseterms:

> {-
> data BaseTerm : (s : Sig) -> Nat -> Type where
>   -- we have symbol terms
>   Sym : {s : Sig} -> {n : Nat} ->
>         (s n) -> BaseTerm s n
>   -- we have terms for the projections      
>   Pr  : {s : Sig} -> (n, i : Nat) -> 
>         {auto smaller: i `LT` n} ->
>         BaseTerm s n
         
> data Term : (s : Sig) -> Nat -> Type where
>   Base  : BaseTerm s n -> Term s n
>   (:::) : BaseTerm s m -> Vect m (Term s n) -> Term s n
> -}

not ok! 
projections must not go left of (:::), and 

  Sym k ::: [Pr n 0, Pr n 1, ... , Pr n (n-1)]

  should be the same as |Sym k| for |k : s n|,

  so don't allow Sym k alone...

better:

> data Term : (s : Sig) -> Nat -> Type where
>   Pr    : {s : Sig} -> {n : Nat} -> 
>           (i: Nat) -> {auto smaller: i `LT` n} -> Term s n
>   (:::) : {s : Sig} -> {m, n : Nat} -> s m -> Vect m (Term s n) -> Term s n








