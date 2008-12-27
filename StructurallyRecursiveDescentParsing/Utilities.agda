------------------------------------------------------------------------
-- A function used by several parser variants
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Utilities where

------------------------------------------------------------------------
-- A suitably typed composition operator

infixr 9 _∘_

_∘_ : {A : Set} {B : A -> Set1} {C : {x : A} -> B x -> Set} ->
      (forall {x} (y : B x) -> C y) -> (g : (x : A) -> B x) ->
      ((x : A) -> C (g x))
f ∘ g = \x -> f (g x)
