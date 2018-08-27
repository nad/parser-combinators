------------------------------------------------------------------------
-- A lookahead operator cannot be defined
------------------------------------------------------------------------

-- In "Parsing with First-Class Derivatives" Brachthäuser, Rendel and
-- Ostermann state that "Lookahead and [...] cannot be expressed as
-- user defined combinators". Here I give a formal proof of a variant
-- of this statement (in the present setting).

module TotalParserCombinators.NoLookahead where

open import Data.List
open import Data.List.Properties
open import Data.Product
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence; _⇔_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary

open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics.Continuation

-- It is impossible to define a lookahead operator satisfying a
-- certain specification (without changing the interface of the parser
-- combinator library).

no-lookahead :
  ¬ ∃ λ (look : ∀ {Tok R} {f-bag : List Tok → List R} →
                ((s : List Tok) → Parser Tok R (f-bag s)) →
                Parser Tok R (f-bag [])) →
      ∀ {Tok R x s₁ s₂} {f-bag : List Tok → List R}
        {f : (s : List Tok) → Parser Tok R (f-bag s)} →
      x ⊕ s₂ ∈ look f · s₁ ⇔ x ⊕ s₂ ∈ f s₁ · s₁
no-lookahead (look , correct) = ¬f[-]·[-] f[-]·[-]
  where
  f-bag : List ⊤ → List ⊤
  f-bag []      = [ _ ]
  f-bag (_ ∷ _) = []

  f : (s : List ⊤) → Parser ⊤ ⊤ (f-bag s)
  f []      = return _
  f (_ ∷ _) = fail

  f[]·[] : _ ⊕ [] ∈ f [] · []
  f[]·[] = return

  look-f·[] : _ ⊕ [] ∈ look f · []
  look-f·[] = Equivalence.from correct ⟨$⟩ f[]·[]

  look-f·[-] : _ ⊕ [ _ ] ∈ look f · [ _ ]
  look-f·[-] = extend look-f·[]

  f[-]·[-] : _ ⊕ [ _ ] ∈ f [ _ ] · [ _ ]
  f[-]·[-] = Equivalence.to correct ⟨$⟩ look-f·[-]

  ¬f[-]·[-] : ¬ _ ⊕ [ _ ] ∈ f [ _ ] · [ _ ]
  ¬f[-]·[-] ()
