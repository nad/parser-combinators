------------------------------------------------------------------------
-- A language of parser equivalence proofs
------------------------------------------------------------------------

-- This module defines yet another set of equivalence relations and
-- preorders for parsers. For symmetric kinds these relations are
-- equalities (compatible equivalence relations) by construction, and
-- they are sound and complete with respect to the previously defined
-- equivalences (see TotalParserCombinators.Congruence.Sound for the
-- soundness proof). This means that parser and language equivalence
-- are also equalities. The related orderings are compatible
-- preorders.

module TotalParserCombinators.Congruence where

open import Codata.Musical.Notation
open import Data.List
open import Data.List.Relation.Binary.BagAndSetEquality
  using (bag) renaming (_∼[_]_ to _List-∼[_]_)
open import Data.Maybe hiding (_>>=_)
open import Data.Nat hiding (_^_)
open import Data.Product
open import Data.Vec.Recursive
open import Function
open import Function.Related using (Symmetric-kind; ⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)

open import TotalParserCombinators.Derivative using (D)
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_∼[_]c_; _∷_)
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
  hiding ([_-_]_⊛_; [_-_]_>>=_)

infixl 50 [_-_]_⊛_ [_-_-_-_]_⊛_ _<$>_
infix  10 [_-_]_>>=_ [_-_-_-_]_>>=_
infixl  5 _∣_
infix   5 _∷_
infix   4 _∼[_]P_ ∞⟨_⟩_∼[_]P_ _≅P_ _≈P_
infix   3 _∎
infixr  2 _∼⟨_⟩_ _≅⟨_⟩_

------------------------------------------------------------------------
-- Helper functions

flatten₁ : {A : Set} → Maybe (Maybe A ^ 2) → Maybe A
flatten₁ nothing        = nothing
flatten₁ (just (m , _)) = m

flatten₂ : {A : Set} → Maybe (Maybe A ^ 2) → Maybe A
flatten₂ nothing        = nothing
flatten₂ (just (_ , m)) = m

------------------------------------------------------------------------
-- Equivalence proof programs

mutual

  _≅P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≅P p₂ = p₁ ∼[ parser ]P p₂

  _≈P_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
  p₁ ≈P p₂ = p₁ ∼[ language ]P p₂

  data _∼[_]P_ {Tok} :
         ∀ {R xs₁ xs₂} →
         Parser Tok R xs₁ → Kind → Parser Tok R xs₂ → Set₁ where

    -- This constructor, which corresponds to CE._∷_, ensures that the
    -- relation is complete.

    _∷_ : ∀ {k R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
          (xs₁≈xs₂ : xs₁ List-∼[ k ] xs₂)
          (Dp₁≈Dp₂ : ∀ t → ∞ (D t p₁ ∼[ k ]P D t p₂)) →
          p₁ ∼[ k ]P p₂

    -- Equational reasoning.

    _∎     : ∀ {k R xs} (p : Parser Tok R xs) → p ∼[ k ]P p

    _∼⟨_⟩_ : ∀ {k R xs₁ xs₂ xs₃}
               (p₁ : Parser Tok R xs₁)
               {p₂ : Parser Tok R xs₂}
               {p₃ : Parser Tok R xs₃}
             (p₁≈p₂ : p₁ ∼[ k ]P p₂) (p₂≈p₃ : p₂ ∼[ k ]P p₃) →
             p₁ ∼[ k ]P p₃

    _≅⟨_⟩_ : ∀ {k R xs₁ xs₂ xs₃}
               (p₁ : Parser Tok R xs₁)
               {p₂ : Parser Tok R xs₂}
               {p₃ : Parser Tok R xs₃}
             (p₁≅p₂ : p₁ ≅P p₂) (p₂≈p₃ : p₂ ∼[ k ]P p₃) →
             p₁ ∼[ k ]P p₃

    sym : ∀ {k : Symmetric-kind} {R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
          (p₁≈p₂ : p₁ ∼[ ⌊ k ⌋ ]P p₂) → p₂ ∼[ ⌊ k ⌋ ]P p₁

    -- Congruences.

    return : ∀ {k R} {x₁ x₂ : R}
             (x₁≡x₂ : x₁ ≡ x₂) → return x₁ ∼[ k ]P return x₂

    fail : ∀ {k R} → fail {R = R} ∼[ k ]P fail {R = R}

    token : ∀ {k} → token ∼[ k ]P token

    _∣_ : ∀ {k R xs₁ xs₂ xs₃ xs₄}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃}
            {p₄ : Parser Tok R xs₄}
          (p₁≈p₃ : p₁ ∼[ k ]P p₃) (p₂≈p₄ : p₂ ∼[ k ]P p₄) →
          p₁ ∣ p₂ ∼[ k ]P p₃ ∣ p₄

    _<$>_ : ∀ {k R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
              {p₁ : Parser Tok R₁ xs₁}
              {p₂ : Parser Tok R₁ xs₂}
            (f₁≗f₂ : f₁ ≗ f₂) (p₁≈p₂ : p₁ ∼[ k ]P p₂) →
            f₁ <$> p₁ ∼[ k ]P f₂ <$> p₂

    [_-_]_⊛_ :
      ∀ {k R₁ R₂} xs₁xs₂ fs₁fs₂ →
      let xs₁ = flatten₁ xs₁xs₂; xs₂ = flatten₂ xs₁xs₂
          fs₁ = flatten₁ fs₁fs₂; fs₂ = flatten₂ fs₁fs₂ in
        {p₁ : ∞⟨ xs₁ ⟩Parser Tok (R₁ → R₂) (flatten fs₁)}
        {p₂ : ∞⟨ fs₁ ⟩Parser Tok  R₁       (flatten xs₁)}
        {p₃ : ∞⟨ xs₂ ⟩Parser Tok (R₁ → R₂) (flatten fs₂)}
        {p₄ : ∞⟨ fs₂ ⟩Parser Tok  R₁       (flatten xs₂)}
      (p₁≈p₃ : ∞⟨ xs₁xs₂ ⟩ p₁ ∼[ k ]P p₃)
      (p₂≈p₄ : ∞⟨ fs₁fs₂ ⟩ p₂ ∼[ k ]P p₄) →
      p₁ ⊛ p₂ ∼[ k ]P p₃ ⊛ p₄

    [_-_]_>>=_ :
      ∀ {k R₁ R₂} (f₁f₂ : Maybe (Maybe (R₁ → List R₂) ^ 2)) xs₁xs₂ →
      let f₁  = flatten₁ f₁f₂;   f₂  = flatten₂ f₁f₂
          xs₁ = flatten₁ xs₁xs₂; xs₂ = flatten₂ xs₁xs₂ in
        {p₁ : ∞⟨ f₁ ⟩Parser Tok R₁ (flatten xs₁)}
        {p₂ : (x : R₁) → ∞⟨ xs₁ ⟩Parser Tok R₂ (apply f₁ x)}
        {p₃ : ∞⟨ f₂ ⟩Parser Tok R₁ (flatten xs₂)}
        {p₄ : (x : R₁) → ∞⟨ xs₂ ⟩Parser Tok R₂ (apply f₂ x)}
      (p₁≈p₃ : ∞⟨ f₁f₂ ⟩ p₁ ∼[ k ]P p₃)
      (p₂≈p₄ : ∀ x → ∞⟨ xs₁xs₂ ⟩ p₂ x ∼[ k ]P p₄ x) →
      p₁ >>= p₂ ∼[ k ]P p₃ >>= p₄

    nonempty : ∀ {k R xs₁ xs₂}
                 {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
               (p₁≈p₂ : p₁ ∼[ k ]P p₂) → nonempty p₁ ∼[ k ]P nonempty p₂

    cast : ∀ {k R xs₁ xs₂ xs₁′ xs₂′}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             {xs₁≈xs₁′ : xs₁ List-∼[ bag ] xs₁′}
             {xs₂≈xs₂′ : xs₂ List-∼[ bag ] xs₂′}
           (p₁≈p₂ : p₁ ∼[ k ]P p₂) →
           cast xs₁≈xs₁′ p₁ ∼[ k ]P cast xs₂≈xs₂′ p₂

  -- Certain proofs can be coinductive if both sides are delayed.

  ∞⟨_⟩_∼[_]P_ :
    ∀ {Tok R xs₁ xs₂} {A : Set} (m₁m₂ : Maybe (Maybe A ^ 2)) →
    ∞⟨ flatten₁ m₁m₂ ⟩Parser Tok R xs₁ → Kind →
    ∞⟨ flatten₂ m₁m₂ ⟩Parser Tok R xs₂ → Set₁
  ∞⟨ nothing ⟩ p₁ ∼[ k ]P p₂ = ∞ (♭  p₁ ∼[ k ]P ♭  p₂)
  ∞⟨ just _  ⟩ p₁ ∼[ k ]P p₂ =    ♭? p₁ ∼[ k ]P ♭? p₂

------------------------------------------------------------------------
-- Some derived combinators

[_-_-_-_]_⊛_ :
  ∀ {k Tok R₁ R₂} xs₁ xs₂ fs₁ fs₂
    {p₁ : ∞⟨ xs₁ ⟩Parser Tok (R₁ → R₂) (flatten fs₁)}
    {p₂ : ∞⟨ fs₁ ⟩Parser Tok  R₁       (flatten xs₁)}
    {p₃ : ∞⟨ xs₂ ⟩Parser Tok (R₁ → R₂) (flatten fs₂)}
    {p₄ : ∞⟨ fs₂ ⟩Parser Tok  R₁       (flatten xs₂)} →
  ♭? p₁ ∼[ k ]P ♭? p₃ → ♭? p₂ ∼[ k ]P ♭? p₄ → p₁ ⊛ p₂ ∼[ k ]P p₃ ⊛ p₄
[ xs₁ - xs₂ - fs₁ - fs₂ ] p₁≈p₃ ⊛ p₂≈p₄ =
  [ just (xs₁ , xs₂) - just (fs₁ , fs₂) ] p₁≈p₃ ⊛ p₂≈p₄

[_-_-_-_]_>>=_ :
  ∀ {k Tok R₁ R₂} (f₁ f₂ : Maybe (R₁ → List R₂)) xs₁ xs₂
    {p₁ : ∞⟨ f₁ ⟩Parser Tok R₁ (flatten xs₁)}
    {p₂ : (x : R₁) → ∞⟨ xs₁ ⟩Parser Tok R₂ (apply f₁ x)}
    {p₃ : ∞⟨ f₂ ⟩Parser Tok R₁ (flatten xs₂)}
    {p₄ : (x : R₁) → ∞⟨ xs₂ ⟩Parser Tok R₂ (apply f₂ x)} →
  ♭? p₁ ∼[ k ]P ♭? p₃ → (∀ x → ♭? (p₂ x) ∼[ k ]P ♭? (p₄ x)) →
  p₁ >>= p₂ ∼[ k ]P p₃ >>= p₄
[ f₁ - f₂ - xs₁ - xs₂ ] p₁≈p₃ >>= p₂≈p₄ =
  [ just (f₁ , f₂) - just (xs₁ , xs₂) ] p₁≈p₃ >>= p₂≈p₄

------------------------------------------------------------------------
-- Completeness

complete : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ∼[ k ] p₂ → p₁ ∼[ k ]P p₂
complete = complete′ ∘ CE.complete
  where
  complete′ : ∀ {k Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁}
                {p₂ : Parser Tok R xs₂} →
              p₁ ∼[ k ]c p₂ → p₁ ∼[ k ]P p₂
  complete′ (xs₁≈xs₂ ∷ Dp₁≈Dp₂) =
    xs₁≈xs₂ ∷ λ t → ♯ complete′ (♭ (Dp₁≈Dp₂ t))
