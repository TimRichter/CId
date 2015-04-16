# CId
a little category theory in Idris

This is an attempt to formalize some elementary category
theory in Idris, to be used in a lecture at Universität Potsdam
in summer 2015. Let's see how far we get.

Supposed to work with the latest cabal version of Idris:
Just do a "cabal update",  "cabal install Idris" and clone this repo.

* What's in the files:

** Category.lidr

Definitions of a category, a functor, a natural transformation.

** FreeCatOnGraph.lidr

Definition of graphs, construction of the free category on a graph.

** FinSet.lidr

The category (or rather a sceleton of the category) of finite sets:
Nat is the type of objects, Hom m n is Vect m (Fin n)  
(rather than (Fin m) -> (Fin n)) to have function extensionality...

Still incomplete.

