# CId
a little category theory in Idris

This is an attempt to formalize some elementary category
theory in Idris, to be used in a lecture at Universität Potsdam
in summer 2015. Let's see how far we get.

Typechecks (mostly, see below) in Idris Version 0.9.19.1

## What's in the files:

### Category.lidr

Definitions of a category, a functor, a natural transformation.

### Graph.lidr

Defines type of directed graphs

### FreeCatOnGraph.lidr

Construction of the free category on a directed graph.

### EqCat.lidr

The discrete category on a type: morphisms are the equalities.

### TypeCat.lidr

Type is a category with maps as morphisms.

### FinSCat.lidr

A sceleton of the category of finite sets:

Nat is the type of objects. 

Hom m n is Vect m (Fin n) (rather than (Fin m) -> (Fin n)) 
to have function extensionality.

### DecProp.lidr

Attempt to model decidable propositions using typeclasses.
Doesn't typecheck.
Not really used so far...

### Prop.lidr

Defines IsProp and proves Uip in some variants.

### Preorder.lidr

Preorders (without Categories). May be unnecessary.

### FunExtAxiom.lidr

Function extensionality axiom. Needed for FunCat and CatCat.

### FunCat.lidr

Functor category ... incomplete.

### CatCat.lidr

Category of categories ... incomplete.

