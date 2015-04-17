> module FinSet
> import Category
> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total

Goal: define the category of finite sets

To get extensional equality of functions (Fin m) -> (Fin n),
we identify such f with the vector [f(0),...,f(m-1)], i.e. an
element of Vect m (Fin n)

the identity functions then become

> idVect : (n:Nat) -> Vect n (Fin n)
> idVect Z = []
> idVect (S n) = FZ :: map FS (idVect n)

composition

> pick : {m:Nat} -> {A:Type} -> (Vect m A) -> Fin m -> A
> pick {m=Z}      _        x       = absurd x
> pick {m=(S m')} (a::_)   FZ      = a
> pick {m=(S m')} (_::as) (FS x')  = pick as x'

> compVect : {l:Nat} -> {m:Nat} -> {n:Nat} ->
>            (Vect m (Fin n)) -> (Vect l (Fin m)) -> 
>            (Vect l (Fin n))
> compVect {l=Z}      _  _       = []
> compVect {l=(S l')} f (gZ::gR) = (pick f gZ) :: (compVect f gR)


for the associativity proof, we'll need

> pickLemma : {l:Nat} -> {m:Nat} -> {n:Nat} ->
>            (f: Vect m (Fin n)) -> (g: Vect l (Fin m)) -> 
>            (x: Fin l) ->
>            pick (compVect f g) x = pick f (pick g x)
>
> pickLemma {l=Z} _ _ x                    = absurd x
> pickLemma {l=(S l')} f (gZ::gR) FZ       = Refl
> pickLemma {l=(S l')} f (gZ::gR) (FS x')  = pickLemma {l=l'} f gR x'
     

 compVectAss : {k:Nat} -> {l:Nat} -> {m:Nat} -> {n:Nat} ->
          (f: Vect m (Fin n)) -> (g: Vect l (Fin m)) -> 
          (h: Vect k (Fin l)) ->
          (compVect (compVect f g) h) = (compVect f (compVect g h))
 compVectAss {k=Z} _ _ _ = Refl
 compVectAss {k=(S k')} f g (hZ::hR) = ?cva

> finC : Cat
> finC = MkCat Nat                        -- objects
>              (\ m => (\ n => Vect m (Fin n)))  -- morphisms
>              idVect                     -- identity
>              compVect                   -- composition
>              ?ass
>              ?idPre
>              ?idPost

Thorsten said FinSet can be given the structure of
a category with families, see Dybjer "Internal Type Theory"
(and also Hofmann: "Syntax and Semantics of Dependent Types"),
He proposed to start with

> inl : (m:Nat) -> (n:Nat) -> Fin m -> Fin (m + n)
> inl Z      n x       = absurd x
> inl (S m') n FZ      = FZ
> inl (S m') n (FS x') = FS (inl m' n x')

> inr : (m:Nat) -> (n:Nat) -> Fin m -> Fin (n + m)
> inr Z      n      x  = absurd x
> inr (S m') Z      x  = x
> inr (S m') (S n') x  = FS (inr (S m') n' x)


