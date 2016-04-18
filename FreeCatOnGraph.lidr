> module FreeCatOnGraph
> import Graph
> import Category
> import Syntax.PreorderReasoning

> %default total
> %auto_implicits off
> %access public export

The free category on a directed graph:

for the morphisms of the free Category, we need 
"heterogeneous" lists

> data HList : (V : Type) -> (E : V -> V -> Type) ->
>              V -> V -> Type          where
>   HLNil  : {V : Type} -> {E : V -> V -> Type} ->
>            {v : V} -> HList V E v v
>   HLConc : {V : Type} -> {E : V -> V -> Type} ->
>            {a, b, c : V} ->
>            (f : HList V E b c) -> (g : E a b) ->
>            HList V E a c

We need concatenation of HLists

> infixl 5 +!+

> (+!+) : {V : Type} -> {E : V -> V -> Type} ->
>         {a, b, c : V} ->
>         HList V E b c -> HList V E a b -> HList V E a c
> x +!+  HLNil       = x
> x +!+ (HLConc f g) = HLConc (x +!+ f) g

, a proof that it is associative

> assHList : {V : Type} -> {E : V -> V -> Type} ->
>            {a, b, c, d : V} ->
>            (f : HList V E c d) -> (g : HList V E b c) ->
>            (h : HList V E a b) ->
>            ((f +!+ g) +!+ h) = (f +!+ (g +!+ h))
>
> assHList f g HLNil = Refl
> assHList f g (HLConc h1 h2) = 
>    ((f +!+ g) +!+ (HLConc h1 h2))
>    ={ Refl }=
>    (HLConc ((f +!+ g) +!+ h1) h2)
>    ={ cong {f=(\ x => HLConc x h2)} (assHList f g h1) }=
>    (HLConc (f +!+ (g +!+ h1)) h2)
>    ={ Refl }=
>    (f +!+ (g +!+ (HLConc h1 h2)))
>    QED

, and a proof that (HLNil +!+ f) = f

> hLNilIdLeft : {V : Type} -> {E : V -> V -> Type} ->
>               {a, b : V} -> (f : HList V E a b) ->
>               (HLNil +!+ f) = f
> hLNilIdLeft HLNil = Refl
> hLNilIdLeft (HLConc fr ff) =
>    (HLNil +!+ (HLConc fr ff))
>    ={ Refl }=
>    (HLConc (HLNil +!+ fr) ff)
>    ={ cong {f = (\x => HLConc x ff)} (hLNilIdLeft fr) }=
>    (HLConc fr ff)
>    QED

> FreeCatOfGraph : Graph -> Cat
> FreeCatOfGraph (MkGraph V E) = 
>    MkCat V (HList V E) fcgId fcgComp fcgAss fcgIL fcgIR  where
>    fcgId : (x : V) -> HList V E x x
>    fcgId x = HLNil {v = x}
>    fcgComp : {a, b, c : V} ->
>      (f: HList V E b c) -> (g : HList V E a b) -> HList V E a c
>    fcgComp = (+!+)
>    fcgAss : {a, b, c, d : V} -> (f : HList V E c d) -> 
>      (g : HList V E b c) -> (h : HList V E a b) ->
>      ((f +!+ g) +!+ h) = (f +!+ (g +!+ h))
>    fcgAss = assHList
>    fcgIL : {a, b : V} -> (f : HList V E a b) ->
>            (f +!+ HLNil) = f
>    fcgIL f = Refl
>    fcgIR : {a, b : V} -> (f : HList V E a b) ->
>            (HLNil +!+ f) = f
>    fcgIR f = hLNilIdLeft f


