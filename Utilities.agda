------------------------------------------------------------------------
-- Some types and functions used by several parser variants
------------------------------------------------------------------------

module Utilities where

open import Data.Product
open import Data.List

------------------------------------------------------------------------
-- Associativity

-- Used to specify how chain₁ and chain should apply the parsed
-- operators: left or right associatively.

data Assoc : Set where
  left  : Assoc
  right : Assoc

------------------------------------------------------------------------
-- Post-processing for the chain₁ parser

-- Application.

appʳ : forall {r} -> r × (r -> r -> r) -> r -> r
appʳ (x , _•_) y = x • y

appˡ : forall {r} -> r -> (r -> r -> r) × r -> r
appˡ x (_•_ , y) = x • y

-- Shifting. See Examples below for an illuminating example.

shift : forall {a b} -> [ a × b ] -> a -> a × [ b × a ]
shift []                x  = (x , [])
shift ((x₁ , x₂) ∷ xs₃) x₄ = (x₁ , (x₂ , proj₁ x₃xs₄) ∷ proj₂ x₃xs₄)
  where x₃xs₄ = shift xs₃ x₄

-- The post-processing function. See Examples below for some
-- illuminating examples.

chain₁-combine : forall {r} -> Assoc -> [ r × (r -> r -> r) ] -> r -> r
chain₁-combine right xs y = foldr appʳ y xs
chain₁-combine left  xs y = uncurry (foldl appˡ) (shift xs y)

private
 module Examples {r s : Set}
                 (x y z : r)
                 (A B : s)
                 (_+_ _*_ : r -> r -> r)
                 where

  open import Logic

  ex : shift ((x , A) ∷ (y , B) ∷ []) z ≡ (x , ((A , y) ∷ (B , z) ∷ []))
  ex = ≡-refl

  exʳ : chain₁-combine right ((x , _+_) ∷ (y , _*_) ∷ []) z ≡ x + (y * z)
  exʳ = ≡-refl

  exˡ : chain₁-combine left  ((x , _+_) ∷ (y , _*_) ∷ []) z ≡ (x + y) * z
  exˡ = ≡-refl
