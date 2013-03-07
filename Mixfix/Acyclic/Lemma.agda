------------------------------------------------------------------------
-- A lemma
------------------------------------------------------------------------

open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph using (acyclic)

module Mixfix.Acyclic.Lemma
         (g : PrecedenceGraphInterface.PrecedenceGraph acyclic)
         where

open import Data.List using ([]; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; foldl; _⁺∷ʳ_)
open import Data.Product using (uncurry)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open PrecedenceCorrect acyclic g
open import Mixfix.Fixity

-- A generalisation of Mixfix.Acyclic.Grammar.Prec.appˡ.

appˡ : ∀ {p} → Outer p left → List⁺ (Outer p left → ExprIn p left) →
       ExprIn p left
appˡ e fs = foldl (λ e f → f (similar e)) (λ f → f e) fs

appˡ-∷ʳ : ∀ {p} (e : Outer p left) fs f →
          appˡ e (fs ⁺∷ʳ f) ≡ f (similar (appˡ e fs))
appˡ-∷ʳ e = uncurry (helper e)
  where
  helper : ∀ {p} (e : Outer p left) f′ fs f →
           appˡ e ((f′ ∷ fs) ⁺∷ʳ f) ≡ f (similar (appˡ e (f′ ∷ fs)))
  helper e f′ []        f = refl
  helper e f′ (f″ ∷ fs) f = helper (similar (f′ e)) f″ fs f
