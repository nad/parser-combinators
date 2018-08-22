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
open import TotalParserCombinators.Semantics

-- It is impossible to define a lookahead operator satisfying a
-- certain specification.
--
-- Note that the proof would go through if the Parser type was
-- extended with more constructors, as long as the semantics of these
-- constructors was specified in the usual way (not by, for instance,
-- giving an extra rule for _⊛_).

no-lookahead :
  ¬ ∃ λ (look : ∀ {Tok R} {f-bag : List Tok → List R} →
                ((s : List Tok) → Parser Tok R (f-bag s)) →
                Parser Tok R (f-bag [])) →
      ∀ {Tok R₁ R₂ xs x s} {f-bag : List Tok → List (R₁ → R₂)}
        {f : (s : List Tok) → Parser Tok (R₁ → R₂) (f-bag s)}
        {p : Parser Tok R₁ xs} →
      x ∈ look f ⊛ p · s ⇔ x ∈ f s ⊛ p · s
no-lookahead (look , correct) = ¬-f-[tt]-⊛-[tt] f-[tt]-⊛-[tt]
  where
  f-bag : List ⊤ → List (⊤ → ⊤)
  f-bag []      = [ _ ]
  f-bag (_ ∷ _) = []

  f : (s : List ⊤) → Parser ⊤ (⊤ → ⊤) (f-bag s)
  f []      = return _
  f (_ ∷ _) = fail

  f-[]-⊛-[] : _ ∈ f [] ⊛ return _ · []
  f-[]-⊛-[] = return ⊛ return

  look-f-⊛-[] : _ ∈ look f ⊛ Parser.return _ · []
  look-f-⊛-[] = Equivalence.from correct ⟨$⟩ f-[]-⊛-[]

  look-f-[] : _ ∈ look f · []
  look-f-[] = lemma look-f-⊛-[]
    where
    lemma : ∀ {s} → _ ∈ look f ⊛ Parser.return _ · s → _ ∈ look f · s
    lemma (∈look ⊛ return) =
      cast∈ PE.refl PE.refl (PE.sym (++-identityʳ _)) ∈look

  look-f-⊛-[tt] : _ ∈ look f ⊛ Parser.token · [ tt ]
  look-f-⊛-[tt] = look-f-[] ⊛ token

  f-[tt]-⊛-[tt] : _ ∈ f [ tt ] ⊛ Parser.token · [ tt ]
  f-[tt]-⊛-[tt] = Equivalence.to correct ⟨$⟩ look-f-⊛-[tt]

  ¬-f-[tt]-⊛-[tt] : ¬ (_ ∈ f [ tt ] ⊛ Parser.token · [ tt ])
  ¬-f-[tt]-⊛-[tt] = λ hyp → case lemma hyp PE.refl of λ ()
    where
    lemma :
      ∀ {s} →
      _ ∈ f [ tt ] ⊛ Parser.token · s →
      s ≡ [ tt ] →
      _ ∈ f [ tt ] · []
    lemma (_⊛_ {s₁ = []}        ∈f token) PE.refl = ∈f
    lemma (_⊛_ {s₁ = _ ∷ []}    _  token) ()
    lemma (_⊛_ {s₁ = _ ∷ _ ∷ _} _  token) ()
