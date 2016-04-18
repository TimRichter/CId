> module FinSCat
> import Category
> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total
> %auto_implicits off
> %access public export

The sceleton of the category of finite sets with
objects Fin n for n in Nat

To get extensional equality of functions (Fin m) -> (Fin n),
we identify such f with the vector [f(0),...,f(m-1)], i.e. an
element of Vect m (Fin n)

> FinMap : Nat -> Nat -> Type
> FinMap m n = Vect m (Fin n)

the identity functions

> idVect : (n : Nat) -> FinMap n n
>
> idVect  Z    = []
> idVect (S n) = FZ :: map FS (idVect n)

composition

Fin m indexes Vect m A :

> pick : {m : Nat} -> {A : Type} -> (Vect m A) -> Fin m -> A
>
> pick {m = Z}       _       x       = absurd x
> pick {m = (S m')} (a::_)   FZ      = a
> pick {m = (S m')} (_::as) (FS x')  = pick as x'

> compVect : {l, m, n : Nat} ->
>            (FinMap m n) -> (FinMap l m) -> (FinMap l n)
>
> compVect f = map (pick f)

for the associativity proof

> pickLemma : {l, m, n:Nat} ->
>            (f: FinMap m n) -> (g: FinMap l m) -> 
>            (x: Fin l) ->
>            pick (compVect f g) x = pick f (pick g x)
>
> pickLemma {l=Z}      _  _          x      = absurd x
> pickLemma {l=(S l')} f (gZ :: gR)  FZ     = Refl
> pickLemma {l=(S l')} f (gZ :: gR) (FS x') = pickLemma {l=l'} f gR x'
     
associativity

> compVectAss : {k, l, m, n : Nat} ->
>          (f: FinMap m n) -> (g: FinMap l m) -> (h: FinMap k l) ->
>          (compVect (compVect f g) h) = (compVect f (compVect g h))
>
> compVectAss {k=Z}      _ _  []          = Refl
> compVectAss {k=(S k')} f g (hZ :: hR)  = 
>   (compVect (compVect f g) (hZ :: hR))
>   ={ Refl }=
>   ((pick (compVect f g) hZ) :: (compVect (compVect f g) hR))
>   ={ cong {f = \x => x :: (compVect (compVect f g) hR)} 
>      (pickLemma f g hZ) }=
>   ((pick f (pick g hZ)) :: (compVect (compVect f g) hR))
>   ={ cong (compVectAss f g hR) }=
>   ((pick f (pick g hZ)) :: (compVect f (compVect g hR)))
>   ={ Refl }=
>   (compVect f (compVect g (hZ :: hR)))
>   QED

idPre and idPost turn out to be trickier

need 3 lemmata

> compVectLemma : {l, m, n : Nat} -> (x : Fin n) ->
>                 (f : FinMap m n) -> (g : FinMap l m) ->
>                 (compVect (x::f) (map FS g) = compVect f g)
>
> compVectLemma {l=Z}      x  _  []     = Refl
> compVectLemma {l=(S l')} x  f (g::gs) =
>   (compVect (x::f) (map FS (g::gs)))
>   ={ Refl }=
>   (pick f g :: compVect (x::f) (map FS gs))
>   ={ cong (compVectLemma x f gs) }=
>   (pick f g :: compVect f gs)
>   ={ Refl }=
>   (compVect f (g::gs))
>   QED

> pickMapLemma : {m : Nat} -> {A, B : Type} -> (f : Vect m A) ->
>                (x : Fin m) -> (g : A -> B) ->
>                pick (map g f) x = g (pick f x)
>
> pickMapLemma {m=Z}       _       x      _ = absurd x
> pickMapLemma {m=(S m')} (fZ::_)  FZ     _ = Refl
> pickMapLemma {m=(S m')} (_::fR) (FS x') g = pickMapLemma {m=m'} fR x' g 

> pickIdPostLemma : {n : Nat} -> (x : Fin n) -> 
>                   (pick (idVect n) x) = x
>
> pickIdPostLemma {n=Z}       x      = absurd x
> pickIdPostLemma {n=(S n')}  FZ     = Refl
> pickIdPostLemma {n=(S n')} (FS x') = 
>   (pick (idVect (S n')) (FS x'))
>   ={ Refl }=
>   (pick (map FS (idVect n')) x')
>   ={ pickMapLemma (idVect n') x' FS }=
>   (FS (pick (idVect n') x'))
>   ={ cong (pickIdPostLemma x') }=
>   (FS x')
>   QED

> idVectPre : {m, n : Nat} -> (f : Vect m (Fin n)) -> 
>             (compVect f (idVect m)) = f
>
> idVectPre {m=Z}      []        = Refl 
> idVectPre {m=(S m')} (fZ::fR)  = 
>   (compVect (fZ::fR) (idVect (S m')))
>   ={ Refl }=
>   ( fZ :: (compVect (fZ::fR) (map FS (idVect m'))))
>   ={ cong (compVectLemma fZ fR (idVect m'))}=
>   ( fZ :: (compVect fR (idVect m')))
>   ={ cong (idVectPre fR) }=
>   (fZ :: fR)
>   QED

> idVectPost :  {m, n : Nat} -> (f : FinMap m n) -> 
>               (compVect (idVect n) f) = f
>
> idVectPost {m=Z}           []       = Refl
> idVectPost {m=(S m')} {n} (fZ::fR)  =
>   (compVect (idVect n) (fZ::fR))
>   ={ Refl }=
>   (pick (idVect n) fZ :: compVect (idVect n) fR)
>   ={ cong {f = \v => v :: compVect (idVect n) fR} (pickIdPostLemma fZ) }=
>   (fZ :: compVect (idVect n) fR)
>   ={ cong (idVectPost {m=m'} fR) }=
>   (fZ :: fR)
>   QED

> finSCat : Cat
> finSCat = MkCat Nat FinMap idVect  compVect                       
>              compVectAss  idVectPre idVectPost

