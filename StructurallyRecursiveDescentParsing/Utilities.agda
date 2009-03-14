------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Utilities where

------------------------------------------------------------------------
-- Some suitably typed composition operators

infixr 9 _∘₁_ _∘₁₁_

_∘₁_ : {A : Set} {B : A -> Set1} {C : {x : A} -> B x -> Set} ->
       (forall {x} (y : B x) -> C y) -> (g : (x : A) -> B x) ->
       ((x : A) -> C (g x))
f ∘₁ g = \x -> f (g x)

_∘₁₁_ : {A : Set} {B : A → Set1} {C : {x : A} → B x → Set1} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘₁₁ g = λ x → f (g x)
