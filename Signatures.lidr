> module Signatures
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total
> %auto_implicits off
> %access public export

A (onesorted) signature is just a type family over |Nat|.
The elements of |sig n| are the n-ary symbols. 

> Sig : Type
> Sig = Nat -> Type

> arity : {s : Sig} -> {n : Nat} -> s n -> Nat
> arity {n} _ = n

The family of n-ary Terms over a signature is a tree 
type where m-ary symbols label the m-branching nodes 
and the leafs are the n-ary "projections" (indexed
by 0,1,...,n-1)

> infixr 7 :::

> data Term : Sig -> Nat -> Type where
>   Pr    : {s : Sig} -> {n : Nat} -> 
>           (i : Nat) -> {auto smaller: i `LT` n} -> Term s n
>   (:::) : {s : Sig} -> {m, n : Nat} -> s m -> Vect m (Term s n) -> Term s n

We could have written 

< data Term : Sig -> Sig

Indeed, we'll show that Sig is a category and Term is a monad 
on Sig.:

morphisms of Sig:

> SigMor : Sig -> Sig -> Type
> SigMor s t = (n : Nat) -> s n -> t n

identity signature morphisms:

> idSigMor : {s : Sig} -> SigMor s s
> idSigMor = (\n => id)

composition of signature morphisms

> compSigMor : 
>   {s, t, u : Sig} ->
>   SigMor t u ->
>   SigMor s t ->
>   SigMor s u 
> compSigMor {s} {t} {u} f g = comp where
>   comp : (n : Nat) -> s n -> u n
>   comp = \n => (\sSymb => f n (g n sSymb))

associativity

> assCompSigMor : 
>   {s, t, u, v : Sig} ->
>   (f : SigMor u v) ->
>   (g : SigMor t u) ->
>   (h : SigMor s t) ->
>   compSigMor (compSigMor f g) h = compSigMor f (compSigMor g h)
> assCompSigMor f g h = Refl

identity precomposition is neutral

> eta : {a, b : Type} ->
>   (f : a -> b) ->
>   f = (\x => f x)
> eta f = Refl

> etaD : {a : Type} ->
>   {b : a -> Type} ->
>   (f : (x : a) -> b x) ->
>   f = (\x => f x)
> etaD f = Refl

> eta2 : {a, b, c : Type} ->
>   (f : a -> b -> c) ->
>   f = (\x => (\y => (f x) y))
> eta2 f = Refl



> etaNested : {a : Type} ->
>   {b, c : a -> Type} ->
>   (f : (x : a) -> b x -> c x) ->
>   (x : a) ->
>   f x = \sSymb => f x sSymb
> etaNested f x = Refl


 idPreCompSigMor :
   {s, t : Sig} ->
   (f : SigMor s t) ->
   compSigMor f idSigMor = f
 idPreCompSigMor f = 
   (compSigMor f idSigMor)
   ={ Refl }= 
   (\n => (\sSymb => (f n) sSymb))
   ={ sym (eta (f n)) }=
   (\n => f n)
   ={ Refl }=
   f
   QED



Term is a functor

> fmapT : 
>   {s, t : Sig} -> 
>   SigMor s t ->
>   SigMor (Term s) (Term t)
> fmapT f _ (Pr i) = (Pr i)
> fmapT {s} {t} f n (sSymb ::: args) = f (arity sSymb) sSymb ::: map (fmapT f n) args

(laws postponed...)

and a monad... need preparations for this:

 Since Terms have (Pr i) at the leaves, it is  easy to weaken an 
 n-Term to an (S n)-Term by adding a dummy variable

> weakenT : {s : Sig} -> {n : Nat} -> Term s n -> Term s (S n)
> weakenT (Pr {n} i {smaller=sm}) = Pr {n = S n} i {smaller = lteSuccRight sm} 
> weakenT (sym ::: args) = sym ::: map weakenT args

  This should be in a lib somewhere...?

> plusOneRightSucc : (n : Nat) -> n + 1 = S n
> plusOneRightSucc Z = Refl
> plusOneRightSucc (S n) = cong (plusOneRightSucc n)

  The vector [Pr 0, Pr 1, ... , Pr n-1]

> stdnVec : {s : Sig} -> (n : Nat) -> Vect n (Term s n)
> stdnVec Z = []
> stdnVec (S n) = replace {P = \x => Vect x (Term s (S n))} (plusOneRightSucc n) 
>                   ((map weakenT (stdnVec n)) ++ [Pr n {smaller = lteRefl}])

  since the index function of Vect needs Fin and we use Nat with an auto smaller,
  we need:

> natToFin' : {n : Nat} -> (i : Nat) -> {auto smaller: i `LT` n} -> Fin n
> natToFin' {n = Z}    i {smaller}   = absurd smaller
> natToFin' {n = S n}  Z             = FZ 
> natToFin' {n = S n} (S i) {smaller = LTESucc sm} 
>                                    = FS (natToFin' {n} i {smaller = sm}) 

Now we can define the unit of the Term monad:

> unitT : {s: Sig} -> SigMor s (Term s)
> unitT {s} n sSymb = sSymb ::: stdnVec n

and its multiplication

> multT : {s: Sig} -> SigMor (Term (Term s)) (Term s)
> multT {s} n (Pr i) = Pr i
> multT {s} n ((Pr j) ::: termsTT_n_m) = 
>   multT {s} n (index (natToFin' j) termsTT_n_m)
> multT {s} n ((symb_l ::: termsT_m_l) ::: termsTT_n_m) =
>   symb_l ::: map (\ term_m => multT {s} n (term_m ::: termsTT_n_m)) termsT_m_l

> revbindT : 
>   {s, t : Sig} ->
>   SigMor s (Term t) ->
>   SigMor (Term s) (Term t)
> revbindT {s} {t} f n termTS_n = multT {s=t} n (fmapT f n termTS_n) 

> compKleisliT :
>   {s, t, u : Sig} ->
>   SigMor t (Term u) ->
>   SigMor s (Term t) ->
>   SigMor s (Term u)
> compKleisliT {s} {t} {u} f g = compSigMor (multT {s=u}) (compSigMor (fmapT f)  g) 



