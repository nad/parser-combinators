------------------------------------------------------------------------
-- A lemma
------------------------------------------------------------------------

open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph using (acyclic)

module Mixfix.Acyclic.Lemma
         (g : PrecedenceGraphInterface.PrecedenceGraph acyclic)
         where

open import Data.List.NonEmpty using (List⁺; [_]; _∷_; foldl; _∷ʳ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open PrecedenceCorrect acyclic g
open import Mixfix.Fixity

-- A generalisation of Mixfix.Acyclic.Grammar.Prec.appˡ.

appˡ : ∀ {p} → Outer p left → List⁺ (Outer p left → ExprIn p left) →
       ExprIn p left
appˡ e fs = foldl (λ e f → f (similar e)) (λ f → f e) fs

appˡ-∷ʳ : ∀ {p} (e : Outer p left) fs f →
          appˡ e (fs ∷ʳ f) ≡ f (similar (appˡ e fs))
appˡ-∷ʳ e [ f′ ]    f = refl
appˡ-∷ʳ e (f′ ∷ fs) f = appˡ-∷ʳ (similar (f′ e)) fs f
