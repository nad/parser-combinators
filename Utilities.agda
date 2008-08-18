------------------------------------------------------------------------
-- Some types and functions used by several parser variants
------------------------------------------------------------------------

module Utilities where

open import Data.Product
open import Data.List
open import Data.Function using (flip)

------------------------------------------------------------------------
-- Associativity

-- Used to specify how chain₁, chain and chain≥ should apply the
-- parsed operators: left or right associatively.

data Assoc : Set where
  left  : Assoc
  right : Assoc

------------------------------------------------------------------------
-- Post-processing for the chain parsers

-- Application.

appʳ : forall {r} -> r × (r -> r -> r) -> r -> r
appʳ (x , _•_) y = x • y

appˡ : forall {r} -> r -> (r -> r -> r) × r -> r
appˡ x (_•_ , y) = x • y

-- Shifting. See Examples below for an illuminating example.

shiftˡ : forall {a b} -> List (a × b) -> a -> a × List (b × a)
shiftˡ []                x  = (x , [])
shiftˡ ((x₁ , x₂) ∷ xs₃) x₄ = (x₁ , (x₂ , proj₁ x₃xs₄) ∷ proj₂ x₃xs₄)
  where x₃xs₄ = shiftˡ xs₃ x₄

-- The post-processing function. See Examples below for some
-- illuminating examples.

chain₁-combine : forall {r} ->
                 Assoc -> List (r × (r -> r -> r)) -> r -> r
chain₁-combine right xs y = foldr appʳ y xs
chain₁-combine left  xs y = uncurry (foldl appˡ) (shiftˡ xs y)

-- Variants.

shiftʳ : forall {a b} -> a -> List (b × a) -> List (a × b) × a
shiftʳ x  []                = ([] , x)
shiftʳ x₁ ((x₂ , x₃) ∷ xs₄) = ((x₁ , x₂) ∷ proj₁ xs₃x₄ , proj₂ xs₃x₄)
  where xs₃x₄ = shiftʳ x₃ xs₄

chain≥-combine : forall {r} ->
                 Assoc -> r -> List ((r -> r -> r) × r) -> r
chain≥-combine right x ys = uncurry (flip (foldr appʳ)) (shiftʳ x ys)
chain≥-combine left  x ys = foldl appˡ x ys

private
 module Examples {r s : Set}
                 (x y z : r)
                 (A B : s)
                 (_+_ _*_ : r -> r -> r)
                 where

  open import Relation.Binary.PropositionalEquality

  ex₁ : shiftˡ ((x , A) ∷ (y , B) ∷ []) z ≡ (x , ((A , y) ∷ (B , z) ∷ []))
  ex₁ = ≡-refl

  ex₁ʳ : chain₁-combine right ((x , _+_) ∷ (y , _*_) ∷ []) z ≡ x + (y * z)
  ex₁ʳ = ≡-refl

  ex₁ˡ : chain₁-combine left  ((x , _+_) ∷ (y , _*_) ∷ []) z ≡ (x + y) * z
  ex₁ˡ = ≡-refl

  ex≥ : shiftʳ x ((A , y) ∷ (B , z) ∷ []) ≡ ((x , A) ∷ (y , B) ∷ [] , z)
  ex≥ = ≡-refl

  ex≥ʳ : chain≥-combine right x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ x + (y * z)
  ex≥ʳ = ≡-refl

  ex≥ˡ : chain≥-combine left  x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ (x + y) * z
  ex≥ˡ = ≡-refl

------------------------------------------------------------------------
-- Some suitably typed composition operators

infixr 9 _∘′_ _∘₂_

_∘′_ : {a c : Set} {b : a -> Set1} ->
       (forall {x} -> b x -> c) -> ((x : a) -> b x) -> (a -> c)
f ∘′ g = \x -> f (g x)

_∘₂_ : {a b c : Set2} -> (b -> c) -> (a -> b) -> (a -> c)
f ∘₂ g = \x -> f (g x)
