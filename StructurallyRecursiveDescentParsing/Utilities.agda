------------------------------------------------------------------------
-- A function used by several parser variants
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Utilities where

------------------------------------------------------------------------
-- A suitably typed composition operator

infixr 9 _∘′_

_∘′_ : {A C : Set} {B : A -> Set1} ->
       (forall {x} -> B x -> C) -> ((x : A) -> B x) -> (A -> C)
f ∘′ g = \x -> f (g x)
