> module Graph

> %default total

directed Graphs:

> data Graph : Type where
>   MkGraph : (GVert: Type) ->                     -- Vertices
>             (GEdg: GVert -> GVert -> Type) ->    -- directed edges 
>             Graph

getters:

> GVert : Graph -> Type
> GVert (MkGraph V _) = V

> GEdg  : (gg : Graph) -> (v : GVert gg) -> 
>         (w : GVert gg) ->
>         Type
> GEdg (MkGraph _ E) v w = E v w

