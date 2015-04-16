> module FinSet
> import Category
> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total

Goal: define the category of finite sets

the identity vector

> idVect : (n:Nat) -> Vect n (Fin n)
> idVect Z = []
> idVect (S n) = FZ :: map FS (idVect n)

> lookup : {m:Nat} -> {A:Type} -> (Vect m A) -> Fin m -> A
> lookup {m=Z}      _        x       = absurd x
> lookup {m=(S m')} (a::_)   FZ      = a
> lookup {m=(S m')} (_::as) (FS x')  = lookup as x'


> compVect : {l:Nat} -> {m:Nat} -> {n:Nat} ->
>            (Vect m (Fin n)) -> (Vect l (Fin m)) -> 
>            (Vect l (Fin n))
> compVect {l=Z}      _  _       = []
> compVect {l=(S l')} f (gZ::gR) = (lookup f gZ) :: (compVect f gR)

> lookupLemma : {l:Nat} -> {m:Nat} -> {n:Nat} ->
>            (f: Vect m (Fin n)) -> (g: Vect l (Fin m)) -> 
>            (x: Fin l) ->
>            lookup (compVect f g) x = lookup f (lookup g x)

 lookupLemma {l=Z} _ _ x       = absurd x
 lookupLemma {l=(S l')} f g FZ =
     lookup (compVect f g) FZ
     ={ Refl }= 
     ...


> compVectAss : {k:Nat} -> {l:Nat} -> {m:Nat} -> {n:Nat} ->
>          (f: Vect m (Fin n)) -> (g: Vect l (Fin m)) -> 
>          (h: Vect k (Fin l)) ->
>          (compVect (compVect f g) h) = (compVect f (compVect g h))
> compVectAss {k=Z} _ _ _ = Refl
> compVectAss {k=(S k')} f g (hZ::hR) = ?cva

> finC : Cat
> finC = MkCat Nat                        -- objects
>              (\ m => (\ n => Vect m (Fin n)))  -- morphisms
>              idVect                     -- identity
>              compVect                   -- composition
>              ?ass
>              ?idPre
>              ?idPost

Thorsten said FinSet can be given the structure of
a category with families, see Dybjer "Internal Type Theory",
he proposed to start with these (but then...?):

> inl : (m:Nat) -> (n:Nat) -> Fin m -> Fin (m + n)
> inl Z      n x       = absurd x
> inl (S m') n FZ      = FZ
> inl (S m') n (FS x') = FS (inl m' n x')

> inr : (m:Nat) -> (n:Nat) -> Fin m -> Fin (n + m)
> inr Z      n      x  = absurd x
> inr (S m') Z      x  = x
> inr (S m') (S n') x  = FS (inr (S m') n' x)


