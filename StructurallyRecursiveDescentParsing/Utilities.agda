------------------------------------------------------------------------
-- A function used by several parser variants
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Utilities where

------------------------------------------------------------------------
-- A suitably typed composition operator

infixr 9 _∘′_

_∘′_ : {a c : Set} {b : a -> Set1} ->
       (forall {x} -> b x -> c) -> ((x : a) -> b x) -> (a -> c)
f ∘′ g = \x -> f (g x)
