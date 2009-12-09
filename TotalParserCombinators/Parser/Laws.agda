------------------------------------------------------------------------
-- Various parser combinator laws
------------------------------------------------------------------------

-- Note that terms like "monad" and "Kleene algebra" are interpreted
-- liberally below.

module TotalParserCombinators.Parser.Laws where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.Function
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.Properties as AnyProp
import Data.List.Properties as ListProp
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary hiding (module Preorder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Nullary

private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)
  open Any.Membership-≡ using (_⊆_)
  open module SetEq {A : Set} =
         Setoid (Any.Membership-≡.set-equality {A})
         using () renaming (_≈_ to _≛_)

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Applicative
open import TotalParserCombinators.Backend.BreadthFirst
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Parser.CoinductiveEquality as CEq
  hiding (sym)
open import TotalParserCombinators.Parser.Lib
open import TotalParserCombinators.Parser.Semantics

------------------------------------------------------------------------
-- Variants of some of the parser combinators

-- These variants hide the use of ∞?.

infixl 10 _⊙_ _⟫=_

_⊙_ : ∀ {Tok R₁ R₂ fs xs} →
      Parser Tok (R₁ → R₂) fs → Parser Tok R₁ xs →
      Parser Tok R₂ (fs ⊛′ xs)
p₁ ⊙ p₂ = ♯? p₁ ⊛ ♯? p₂

_⟫=_ : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂} →
       Parser Tok R₁ xs → ((x : R₁) → Parser Tok R₂ (f x)) →
       Parser Tok R₂ (xs >>=′ f)
p₁ ⟫= p₂ = p₁ >>= λ x → ♯? (p₂ x)

------------------------------------------------------------------------
-- The relation _⊑_ is a partial order with respect to _≈_

module PartialOrder where

  refl : ∀ {Tok R xs} {p : Parser Tok R xs} → p ⊑ p
  refl = id

  trans : ∀ {Tok R xs₁ xs₂ xs₃}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃} →
          p₁ ⊑ p₂ → p₂ ⊑ p₃ → p₁ ⊑ p₃
  trans p₁⊑p₂ p₂⊑p₃ = p₂⊑p₃ ∘ p₁⊑p₂

  antisym : ∀ {Tok R xs₁ xs₂}
              {p₁ : Parser Tok R xs₁}
              {p₂ : Parser Tok R xs₂} →
            p₁ ⊑ p₂ → p₂ ⊑ p₁ → p₁ ≈ p₂
  antisym p₁⊑p₂ p₂⊑p₁ = ((λ {_} → p₁⊑p₂) , λ {_} → p₂⊑p₁)

------------------------------------------------------------------------
-- The relation _≈_ is an equality, i.e. a congruential equivalence
-- relation

module Equivalence where

  refl : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≈ p
  refl = ((λ {_} → PartialOrder.refl) , λ {_} → PartialOrder.refl)

  sym : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → p₂ ≈ p₁
  sym = swap

  trans : ∀ {Tok R xs₁ xs₂ xs₃}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃} →
          p₁ ≈ p₂ → p₂ ≈ p₃ → p₁ ≈ p₃
  trans = Prod.zip PartialOrder.trans (flip PartialOrder.trans)

♭♯-cong : ∀ {Tok R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → ♭? (♯? {xs = ys₁} p₁) ≈ ♭? (♯? {xs = ys₂} p₂)
♭♯-cong ys₁ ys₂ = Prod.map (helper ys₁ ys₂) (helper ys₂ ys₁)
  where
  helper : ∀ {Tok R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ⊑ p₂ → ♭? (♯? {xs = ys₁} p₁) ⊑ ♭? (♯? {xs = ys₂} p₂)
  helper ys₁ ys₂ p₁⊑p₂ ∈p₁ = add-♭♯ ys₂ $ p₁⊑p₂ $ drop-♭♯ ys₁ ∈p₁

return-cong : ∀ {Tok R} {x₁ x₂ : R} →
              x₁ ≡ x₂ → return {Tok} x₁ ≈ return x₂
return-cong P.refl = Equivalence.refl

fail-cong : ∀ {Tok R} → fail {Tok} {R} ≈ fail {Tok} {R}
fail-cong = Equivalence.refl

token-cong : ∀ {Tok} → token {Tok} ≈ token {Tok}
token-cong = Equivalence.refl

∣-cong : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂}
           {p₃ : Parser Tok R xs₃}
           {p₄ : Parser Tok R xs₄} →
         p₁ ≋ p₃ → p₂ ≋ p₄ → p₁ ∣ p₂ ≋ p₃ ∣ p₄
∣-cong (init₁ ∷ rest₁) (init₂ ∷ rest₂) =
  Prod.zip _++-mono_ _++-mono_ init₁ init₂ ∷ λ t →
  ♯ ∣-cong (♭ (rest₁ t)) (♭ (rest₂ t))
  where open AnyProp.Membership-≡

<$>-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → R₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : Parser Tok R₁ xs₂} →
           f₁ ≗ f₂ → p₁ ≋ p₂ → f₁ <$> p₁ ≋ f₂ <$> p₂
<$>-cong f₁≗f₂ (init ∷ rest) =
  Prod.map (lemma f₁≗f₂) (lemma (P.sym ∘ f₁≗f₂)) init ∷ λ t →
  ♯ <$>-cong f₁≗f₂ (♭ (rest t))
  where
  open Any.Membership-≡.⊆-Reasoning

  lemma : ∀ {A B : Set} {f₁ f₂ : A → B} {xs ys} →
          f₁ ≗ f₂ → xs ⊆ ys → List.map f₁ xs ⊆ List.map f₂ ys
  lemma {f₁ = f₁} {f₂} {xs} {ys} f₁≗f₂ xs⊆ys = begin
    List.map f₁ xs ≡⟨ ListProp.map-cong f₁≗f₂ xs ⟩
    List.map f₂ xs ⊆⟨ AnyProp.Membership-≡.map-mono xs⊆ys ⟩
    List.map f₂ ys ∎

⊛-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
           {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
           {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
           {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
         ♭? p₁ ≈ ♭? p₃ → ♭? p₂ ≈ ♭? p₄ → p₁ ⊛ p₂ ≈ p₃ ⊛ p₄
⊛-cong = Prod.zip helper helper
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
             {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
             {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
             {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
             {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
           ♭? p₁ ⊑ ♭? p₃ → ♭? p₂ ⊑ ♭? p₄ → p₁ ⊛ p₂ ⊑ p₃ ⊛ p₄
  helper ₁⊑₃ ₂⊑₄ (∈p₁ ⊛ ∈p₂) = ₁⊑₃ ∈p₁ ⊛ ₂⊑₄ ∈p₂

⊙-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok (R₁ → R₂) xs₁}
           {p₂ : Parser Tok R₁        xs₂}
           {p₃ : Parser Tok (R₁ → R₂) xs₃}
           {p₄ : Parser Tok R₁        xs₄} →
         p₁ ≈ p₃ → p₂ ≈ p₄ → p₁ ⊙ p₂ ≈ p₃ ⊙ p₄
⊙-cong {xs₁ = xs₁} {xs₂} {xs₃} {xs₄} ₁≈₃ ₂≈₄ =
  ⊛-cong (♭♯-cong xs₂ xs₄ ₁≈₃) (♭♯-cong xs₁ xs₃ ₂≈₄)

>>=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ≈ p₂₁ → (∀ x → ♭? (p₁₂ x) ≈ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ≈ p₂₁ >>= p₂₂
>>=-cong ₁₁≈₂₁ ₁₂≈₂₂ = ((λ {_} → helper (proj₁ ₁₁≈₂₁) (proj₁ ∘ ₁₂≈₂₂))
                       , λ {_} → helper (proj₂ ₁₁≈₂₁) (proj₂ ∘ ₁₂≈₂₂))
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ⊑ p₂₁ → (∀ x → ♭? (p₁₂ x) ⊑ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ⊑ p₂₁ >>= p₂₂
  helper ₁₁⊑₂₁ ₁₂⊑₂₂ (∈p₁₁ >>= ∈p₁₂) = ₁₁⊑₂₁ ∈p₁₁ >>= ₁₂⊑₂₂ _ ∈p₁₂

⟫=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
            {p₁₁ : Parser Tok R₁ xs₁}
            {p₁₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
            {p₂₁ : Parser Tok R₁ xs₂}
            {p₂₂ : (x : R₁) → Parser Tok R₂ (f₂ x)} →
          p₁₁ ≈ p₂₁ → (∀ x → p₁₂ x ≈ p₂₂ x) →
          p₁₁ ⟫= p₁₂ ≈ p₂₁ ⟫= p₂₂
⟫=-cong {xs₁ = xs₁} {xs₂} ₁₁≈₂₁ ₁₂≈₂₂ =
  >>=-cong ₁₁≈₂₁ (♭♯-cong xs₁ xs₂ ∘ ₁₂≈₂₂)

>>=!-cong : ∀ {Tok R₁ R₂ xs₁ xs₂}
              {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
              {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₁}
              {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
              {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₂} →
            ♭ p₁₁ ≈ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ≈ ♭? (p₂₂ x)) →
            p₁₁ >>=! p₁₂ ≈ p₂₁ >>=! p₂₂
>>=!-cong ₁₁≈₂₁ ₁₂≈₂₂ = ((λ {_} → helper (proj₁ ₁₁≈₂₁) (proj₁ ∘ ₁₂≈₂₂))
                        , λ {_} → helper (proj₂ ₁₁≈₂₁) (proj₂ ∘ ₁₂≈₂₂))
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂}
             {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₁}
             {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₂} →
           ♭ p₁₁ ⊑ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ⊑ ♭? (p₂₂ x)) →
           p₁₁ >>=! p₁₂ ⊑ p₂₁ >>=! p₂₂
  helper ₁₁⊑₂₁ ₁₂⊑₂₂ (∈p₁₁ >>=! ∈p₁₂) = ₁₁⊑₂₁ ∈p₁₁ >>=! ₁₂⊑₂₂ _ ∈p₁₂

nonempty-cong : ∀ {Tok R xs₁ xs₂}
                  {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
                p₁ ≋ p₂ → nonempty p₁ ≋ nonempty p₂
nonempty-cong (_ ∷ rest) = SetEq.refl ∷ rest

cast-cong : ∀ {Tok R xs₁ xs₂ xs₁′ xs₂′}
              {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
              {eq₁ : xs₁ ≡ xs₁′} {eq₂ : xs₂ ≡ xs₂′} →
            p₁ ≋ p₂ → cast eq₁ p₁ ≋ cast eq₂ p₂
cast-cong {eq₁ = P.refl} {P.refl} (init ∷ rest) = init ∷ rest

⋆-cong : ∀ {Tok R} {p₁ p₂ : Parser Tok R []} →
         p₁ ≈ p₂ → p₁ ⋆ ≈ p₂ ⋆
⋆-cong = Prod.map helper helper
  where
  helper : ∀ {Tok R} {p₁ p₂ : Parser Tok R []} →
           p₁ ⊑ p₂ → p₁ ⋆ ⊑ p₂ ⋆
  helper {p₁ = p₁} {p₂} p₁⊑p₂ =
    KleeneStar.complete ∘ helper′ ∘ KleeneStar.sound
    where
    helper′ : ∀ {xs s} → xs ∈[ p₁ ]⋆· s → xs ∈[ p₂ ]⋆· s
    helper′ []           = []
    helper′ (∈p₁ ∷ ∈p₁⋆) = p₁⊑p₂ ∈p₁ ∷ helper′ ∈p₁⋆

^-cong : ∀ {Tok R xs₁ xs₂ n}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → p₁ ^ n ≈ p₂ ^ n
^-cong {n = n} = Prod.map (helper n) (helper n)
  where
  helper : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} n →
           p₁ ⊑ p₂ → p₁ ^ n ⊑ p₂ ^ n
  helper                   zero    p₁⊑p₂ return       = return
  helper {xs₁ = xs₁} {xs₂} (suc n) p₁⊑p₂ (∈∷p₁ ⊛ ∈p₁ⁱ)
    with drop-♭♯ (^-initial xs₁ n) ∈∷p₁
  ... | <$> ∈p₁ =
    add-♭♯ (^-initial xs₂ n) (<$> (p₁⊑p₂ ∈p₁)) ⊛
    add-♭♯ (List.map _∷_ xs₂)
           (helper n p₁⊑p₂ (drop-♭♯ (List.map _∷_ xs₁) ∈p₁ⁱ))

↑-cong : ∀ {Tok R xs₁ xs₂ n₁ n₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → n₁ ≡ n₂ → p₁ ↑ n₁ ≈ p₂ ↑ n₂
↑-cong {n₁ = n} p₁≈p₂ P.refl =
  CEq.sound $ <$>-cong (λ _ → P.refl) (CEq.complete $ ^-cong p₁≈p₂)

------------------------------------------------------------------------
-- _∣_ and fail form an idempotent commutative monoid

module AdditiveMonoid where

  commutative : ∀ {Tok R xs₁ xs₂}
                (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
                p₁ ∣ p₂ ≋ p₂ ∣ p₁
  commutative {xs₁ = xs₁} {xs₂} p₁ p₂ =
    lemma ∷ λ t → ♯ commutative (∂ p₁ t) (∂ p₂ t)
    where
    lemma = ((λ {_} → AnyProp.Membership-≡.++-comm xs₁ xs₂)
            , λ {_} → AnyProp.Membership-≡.++-comm xs₂ xs₁)

  left-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → fail ∣ p ≋ p
  left-identity p = SetEq.refl ∷ λ t → ♯ left-identity (∂ p t)

  right-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ fail ≋ p
  right-identity {xs = xs} p =
    lemma ∷ λ t → ♯ right-identity (∂ p t)
    where lemma = SetEq.reflexive (proj₂ ListMonoid.identity xs)

  associative : ∀ {Tok R xs₁ xs₂ xs₃}
                (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂)
                (p₃ : Parser Tok R xs₃) →
                p₁ ∣ (p₂ ∣ p₃) ≋ (p₁ ∣ p₂) ∣ p₃
  associative {xs₁ = xs₁} {xs₂} {xs₃} p₁ p₂ p₃ =
    lemma ∷ λ t → ♯ associative (∂ p₁ t) (∂ p₂ t) (∂ p₃ t)
    where
    lemma = SetEq.reflexive (P.sym $ ListMonoid.assoc xs₁ xs₂ xs₃)

  idempotent : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ p ≋ p
  idempotent {xs = xs} p = lemma ∷ λ t → ♯ idempotent (∂ p t)
    where
    lemma = ((λ {_} → AnyProp.Membership-≡.++-idempotent)
            , λ {_} → AnyProp.++⁺ˡ {xs = xs})

------------------------------------------------------------------------
-- A variant of _⊑_

infix 4 _≤_

-- The AdditiveMonoid module shows that _∣_ can be viewed as the join
-- operation of a join-semilattice. This means that the following
-- definition of order is natural.

_≤_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≤ p₂ = p₁ ∣ p₂ ≈ p₂

-- This order coincides with _⊑_.

⊑⇔≤ : ∀ {Tok R xs₁ xs₂}
      (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
      p₁ ⊑ p₂ ⇔ p₁ ≤ p₂
⊑⇔≤ {xs₁ = xs₁} p₁ p₂ =
  ((λ p₁⊑p₂ → ((λ {_} → helper₁ p₁⊑p₂) , λ {_} → ∣ʳ xs₁))
  , helper₂
  )
  where
  helper₁ : p₁ ⊑ p₂ → p₁ ∣ p₂ ⊑ p₂
  helper₁ p₁⊑p₂ (∣ˡ      s∈p₁) = p₁⊑p₂ s∈p₁
  helper₁ p₁⊑p₂ (∣ʳ .xs₁ s∈p₂) = s∈p₂

  helper₂ : p₁ ≤ p₂ → p₁ ⊑ p₂
  helper₂ (p₁∣p₂⊑p₂ , _) s∈p₁ = p₁∣p₂⊑p₂ (∣ˡ s∈p₁)

------------------------------------------------------------------------
-- _⊙_ and return form an applicative functor

module ApplicativeFunctor where

  identity : ∀ {Tok R xs} (p : Parser Tok R xs) → return id ⊙ p ≈ p
  identity {xs = xs} p =
    ((λ {_} → helper) , λ {_} x∈p → add-♭♯ xs return ⊛ x∈p)
    where
    helper : return id ⊙ p ⊑ p
    helper (∈ret ⊛ ∈p) with drop-♭♯ xs ∈ret
    ... | return = ∈p

  composition :
    ∀ {Tok R₁ R₂ R₃ fs gs xs}
    (p₁ : Parser Tok (R₂ → R₃) fs)
    (p₂ : Parser Tok (R₁ → R₂) gs)
    (p₃ : Parser Tok R₁        xs) →
    return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃ ≈ p₁ ⊙ (p₂ ⊙ p₃)
  composition {fs = fs} {gs} {xs} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃ ⊑ p₁ ⊙ (p₂ ⊙ p₃)
    helper₁ (∈∘p₁p₂ ⊛ ∈p₃) with drop-♭♯ xs ∈∘p₁p₂
    ... | ∈∘p₁ ⊛ ∈p₂ with drop-♭♯ gs ∈∘p₁
    ... | _⊛_ {s₂ = s₁} ∈∘ ∈p₁ with drop-♭♯ fs ∈∘
    ... | return =
      cast∈ P.refl P.refl (P.sym $ ListMonoid.assoc s₁ _ _) $
        add-♭♯ (gs ⊛′ xs) ∈p₁ ⊛
        add-♭♯ fs (add-♭♯ xs (drop-♭♯ ([ _∘′_ ] ⊛′ fs)       ∈p₂) ⊛
                   add-♭♯ gs (drop-♭♯ ([ _∘′_ ] ⊛′ fs ⊛′ gs) ∈p₃))

    helper₂ : p₁ ⊙ (p₂ ⊙ p₃) ⊑ return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃
    helper₂ (_⊛_ {s₁ = s₁} ∈p₁ ∈p₂p₃) with drop-♭♯ fs ∈p₂p₃
    ... | ∈p₂ ⊛ ∈p₃ =
      cast∈ P.refl P.refl (ListMonoid.assoc s₁ _ _) $
        add-♭♯ xs (add-♭♯ gs (add-♭♯ fs return ⊛
                              drop-♭♯ (gs ⊛′ xs) ∈p₁) ⊛
                   add-♭♯ ([ _∘′_ ] ⊛′ fs) (drop-♭♯ xs ∈p₂)) ⊛
        add-♭♯ ([ _∘′_ ] ⊛′ fs ⊛′ gs) (drop-♭♯ gs ∈p₃)

  homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) (x : R₁) →
                 return f ⊙ return x ≈ return {Tok = Tok} (f x)
  homomorphism {Tok} f x = ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : return f ⊙ return x ⊑ return {Tok = Tok} (f x)
    helper₁ (return ⊛ return) = return

    helper₂ : return {Tok = Tok} (f x) ⊑ return f ⊙ return x
    helper₂ return = return {x = f} ⊛ return

  interchange : ∀ {Tok R₁ R₂ fs}
                (p : Parser Tok (R₁ → R₂) fs) (x : R₁) →
                p ⊙ return x ≈ return (λ f → f x) ⊙ p
  interchange {fs = fs} p x = ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p ⊙ return x ⊑ return (λ f → f x) ⊙ p
    helper₁ (∈p ⊛ ∈ret) with drop-♭♯ fs ∈ret
    ... | return =
      cast∈ P.refl P.refl (P.sym $ proj₂ ListMonoid.identity _) $
        add-♭♯ fs return ⊛ ∈p

    helper₂ : return (λ f → f x) ⊙ p ⊑ p ⊙ return x
    helper₂ (∈ret ⊛ ∈p) with drop-♭♯ fs ∈ret
    ... | return =
      cast∈ P.refl P.refl (proj₂ ListMonoid.identity _) $
        ∈p ⊛ add-♭♯ fs return

------------------------------------------------------------------------
-- _⟫=_ and return form a monad

module Monad where

  left-identity : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                  (x : R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
                  return x ⟫= p ≈ p x
  left-identity x p =
    ((λ {_} → helper) , λ {_} → _>>=_ {p₂ = λ y → ⟨ p y ⟩} return)
    where
    helper : return x ⟫= p ⊑ p x
    helper (return >>= ∈px) = ∈px

  right-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → p ⟫= return ≈ p
  right-identity {xs = xs} p =
    ((λ {_} → helper)
    , λ {_} ∈p → cast∈ P.refl P.refl (proj₂ ListMonoid.identity _) $
                   ∈p >>= add-♭♯ xs return)
    where
    helper : p ⟫= return ⊑ p
    helper (∈p >>= ∈ret) with drop-♭♯ xs ∈ret
    ... | return =
      cast∈ P.refl P.refl (P.sym $ proj₂ ListMonoid.identity _) ∈p

  associative : ∀ {Tok R₁ R₂ R₃ xs}
                  {f : R₁ → List R₂} {g : R₂ → List R₃}
                (p₁ : Parser Tok R₁ xs)
                (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                (p₃ : (x : R₂) → Parser Tok R₃ (g x)) →
                (p₁ ⟫= λ x → p₂ x ⟫= p₃) ≈ p₁ ⟫= p₂ ⟫= p₃
  associative {xs = xs} {f} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : (p₁ ⟫= λ x → p₂ x ⟫= p₃) ⊑ p₁ ⟫= p₂ ⟫= p₃
    helper₁ (_>>=_ {x = x} {s₁ = s₁} ∈p₁ ∈p₂xp₃) with drop-♭♯ xs ∈p₂xp₃
    ... | ∈p₂x >>= ∈p₃ =
      cast∈ P.refl P.refl (ListMonoid.assoc s₁ _ _) $
        (∈p₁ >>= add-♭♯ xs ∈p₂x) >>=
        add-♭♯ (xs >>=′ f) (drop-♭♯ (f x) ∈p₃)

    helper₂ : p₁ ⟫= p₂ ⟫= p₃ ⊑ (p₁ ⟫= λ x → p₂ x ⟫= p₃)
    helper₂ ((_>>=_ {x = x} {s₁ = s₁} ∈p₁ ∈p₂) >>= ∈p₃) =
      cast∈ P.refl P.refl (P.sym $ ListMonoid.assoc s₁ _ _) $
        ∈p₁ >>= add-♭♯ xs (drop-♭♯ xs ∈p₂ >>=
                           add-♭♯ (f x) (drop-♭♯ (xs >>=′ f) ∈p₃))

------------------------------------------------------------------------
-- fail is a zero for _⊙_ and _⟫=_, and both _⊙_ and _⟫=_ distribute
-- over _∣_

-- Together with the laws above this means that we have something
-- which resembles an idempotent semiring (both for _⊙_ and for _⟫=_).

module ⊙-IdempotentSemiring where

  open AdditiveMonoid     public
  open ApplicativeFunctor public

  left-zero : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
              fail ⊙ p ≈ fail {R = R₂}
  left-zero {R₂ = R₂} {xs = xs} p = ((λ {_} → helper) , λ {_} ())
    where
    helper : fail ⊙ p ⊑ fail {R = R₂}
    helper (∈fail ⊛ _) with drop-♭♯ xs ∈fail
    ... | ()

  right-zero : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
               p ⊙ fail ≈ fail
  right-zero {fs = fs} p = ((λ {_} → helper) , λ {_} ())
    where
    helper : p ⊙ fail ⊑ fail
    helper (_ ⊛ ∈fail) with drop-♭♯ fs ∈fail
    ... | ()

  left-distributive : ∀ {Tok R₁ R₂ fs xs₁ xs₂}
                      (p₁ : Parser Tok (R₁ → R₂) fs)
                      (p₂ : Parser Tok R₁ xs₁)
                      (p₃ : Parser Tok R₁ xs₂) →
                      p₁ ⊙ (p₂ ∣ p₃) ≈ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
  left-distributive {fs = fs} {xs₁} {xs₂} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p₁ ⊙ (p₂ ∣ p₃) ⊑ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
    helper₁ (∈p₁ ⊛ ∈p₂∣p₃) with drop-♭♯ fs ∈p₂∣p₃
    ... | ∣ˡ      ∈p₂ = ∣ˡ (add-♭♯ xs₁ (drop-♭♯ (xs₁ ++ xs₂) ∈p₁) ⊛
                            add-♭♯ fs                        ∈p₂)
    ... | ∣ʳ .xs₁ ∈p₃ = ∣ʳ (fs ⊛′ xs₁)
                           (add-♭♯ xs₂ (drop-♭♯ (xs₁ ++ xs₂) ∈p₁) ⊛
                            add-♭♯ fs                        ∈p₃)

    helper₂ : p₁ ⊙ p₂ ∣ p₁ ⊙ p₃ ⊑ p₁ ⊙ (p₂ ∣ p₃)
    helper₂ (∣ˡ (∈p₁ ⊛ ∈p₂)) =
      add-♭♯ (xs₁ ++ xs₂)     (drop-♭♯ xs₁ ∈p₁) ⊛
      add-♭♯ fs           (∣ˡ (drop-♭♯ fs  ∈p₂))
    helper₂ (∣ʳ .(fs ⊛′ xs₁) (∈p₁ ⊛ ∈p₃)) =
      add-♭♯ (xs₁ ++ xs₂)         (drop-♭♯ xs₂ ∈p₁) ⊛
      add-♭♯ fs           (∣ʳ xs₁ (drop-♭♯ fs  ∈p₃))

  right-distributive : ∀ {Tok R₁ R₂ fs₁ fs₂ xs}
                       (p₁ : Parser Tok (R₁ → R₂) fs₁)
                       (p₂ : Parser Tok (R₁ → R₂) fs₂)
                       (p₃ : Parser Tok R₁ xs) →
                       (p₁ ∣ p₂) ⊙ p₃ ≈ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
  right-distributive {fs₁ = fs₁} {fs₂} {xs} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : (p₁ ∣ p₂) ⊙ p₃ ⊑ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
    helper₁ (∈p₁∣p₂ ⊛ ∈p₃) with drop-♭♯ xs ∈p₁∣p₂
    ... | ∣ˡ      ∈p₁ = ∣ˡ (add-♭♯ xs                        ∈p₁ ⊛
                            add-♭♯ fs₁ (drop-♭♯ (fs₁ ++ fs₂) ∈p₃))
    ... | ∣ʳ .fs₁ ∈p₂ = ∣ʳ (fs₁ ⊛′ xs)
                        (add-♭♯ xs                        ∈p₂ ⊛
                         add-♭♯ fs₂ (drop-♭♯ (fs₁ ++ fs₂) ∈p₃))

    helper₂ : p₁ ⊙ p₃ ∣ p₂ ⊙ p₃ ⊑ (p₁ ∣ p₂) ⊙ p₃
    helper₂ (∣ˡ (∈p₁ ⊛ ∈p₃)) =
      add-♭♯ xs           (∣ˡ (drop-♭♯ xs  ∈p₁)) ⊛
      add-♭♯ (fs₁ ++ fs₂)     (drop-♭♯ fs₁ ∈p₃)
    helper₂ (∣ʳ .(fs₁ ⊛′ xs) (∈p₂ ⊛ ∈p₃)) =
      add-♭♯ xs           (∣ʳ fs₁ (drop-♭♯ xs  ∈p₂)) ⊛
      add-♭♯ (fs₁ ++ fs₂)         (drop-♭♯ fs₂ ∈p₃)

module ⟫=-IdempotentSemiring where

  open AdditiveMonoid public
    renaming ( associative    to ∣-associative
             ; left-identity  to ∣-left-identity
             ; right-identity to ∣-right-identity
             )
  open Monad public
    renaming ( associative    to ⟫=-associative
             ; left-identity  to ⟫=-left-identity
             ; right-identity to ⟫=-right-identity
             )

  left-zero : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
              (p : (x : R₁) → Parser Tok R₂ (f x)) → fail ⟫= p ≈ fail
  left-zero {f = f} p = ((λ {_} → helper) , λ {_} ())
    where
    helper : fail ⟫= p ⊑ fail
    helper (() >>= _)

  right-zero : ∀ {Tok R₁ R₂ xs}
               (p : Parser Tok R₁ xs) → p ⟫= const fail ≈ fail {R = R₂}
  right-zero {R₂ = R₂} {xs} p = ((λ {_} → helper) , λ {_} ())
    where
    helper : p ⟫= const fail ⊑ fail {R = R₂}
    helper (_ >>= ∈fail) with drop-♭♯ xs ∈fail
    ... | ()

  left-distributive : ∀ {Tok R₁ R₂ xs} {f g : R₁ → List R₂}
                      (p₁ : Parser Tok R₁ xs)
                      (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                      (p₃ : (x : R₁) → Parser Tok R₂ (g x)) →
                      p₁ ⟫= (λ x → p₂ x ∣ p₃ x) ≈ p₁ ⟫= p₂ ∣ p₁ ⟫= p₃
  left-distributive {xs = xs} {f} {g} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p₁ ⟫= (λ x → p₂ x ∣ p₃ x) ⊑ p₁ ⟫= p₂ ∣ p₁ ⟫= p₃
    helper₁ (_>>=_ {x = x} ∈p₁ ∈p₂∣p₃) with drop-♭♯ xs ∈p₂∣p₃
    ... | ∣ˡ        ∈p₂ = ∣ˡ             (∈p₁ >>= add-♭♯ xs ∈p₂)
    ... | ∣ʳ .(f x) ∈p₃ = ∣ʳ (xs >>=′ f) (∈p₁ >>= add-♭♯ xs ∈p₃)

    helper₂ : p₁ ⟫= p₂ ∣ p₁ ⟫= p₃ ⊑ p₁ ⟫= (λ x → p₂ x ∣ p₃ x)
    helper₂ (∣ˡ (∈p₁ >>= ∈p₂)) = ∈p₁ >>= add-♭♯ xs (∣ˡ (drop-♭♯ xs ∈p₂))
    helper₂ (∣ʳ .(xs >>=′ f) (_>>=_ {x = x} ∈p₁ ∈p₃)) =
      ∈p₁ >>= add-♭♯ xs (∣ʳ (f x) (drop-♭♯ xs ∈p₃))

  right-distributive : ∀ {Tok R₁ R₂ xs₁ xs₂} {f : R₁ → List R₂}
                       (p₁ : Parser Tok R₁ xs₁)
                       (p₂ : Parser Tok R₁ xs₂)
                       (p₃ : (x : R₁) → Parser Tok R₂ (f x)) →
                       (p₁ ∣ p₂) ⟫= p₃ ≈ p₁ ⟫= p₃ ∣ p₂ ⟫= p₃
  right-distributive {xs₁ = xs₁} {xs₂} {f} p₁ p₂ p₃ =
    ((λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : (p₁ ∣ p₂) ⟫= p₃ ⊑ p₁ ⟫= p₃ ∣ p₂ ⟫= p₃
    helper₁ (∣ˡ      ∈p₁ >>= ∈p₃) =
      ∣ˡ              (∈p₁ >>= add-♭♯ xs₁ (drop-♭♯ (xs₁ ++ xs₂) ∈p₃))
    helper₁ (∣ʳ .xs₁ ∈p₂ >>= ∈p₃) =
      ∣ʳ (xs₁ >>=′ f) (∈p₂ >>= add-♭♯ xs₂ (drop-♭♯ (xs₁ ++ xs₂) ∈p₃))

    helper₂ : p₁ ⟫= p₃ ∣ p₂ ⟫= p₃ ⊑ (p₁ ∣ p₂) ⟫= p₃
    helper₂ (∣ˡ               (∈p₁ >>= ∈p₃)) =
      ∣ˡ ∈p₁ >>= add-♭♯ (xs₁ ++ xs₂) (drop-♭♯ xs₁ ∈p₃)
    helper₂ (∣ʳ .(xs₁ >>=′ f) (∈p₂ >>= ∈p₃)) =
      ∣ʳ xs₁ ∈p₂ >>= add-♭♯ (xs₁ ++ xs₂) (drop-♭♯ xs₂ ∈p₃)

------------------------------------------------------------------------
-- A limited notion of *-continuity

module *-Continuity where

  -- For argument parsers which are not nullable we can prove that the
  -- Kleene star operator is *-continuous.

  upper-bound : ∀ {Tok R₁ R₂ R₃ fs xs}
                (p₁ : Parser Tok (List R₁ → R₂ → R₃) fs)
                (p₂ : Parser Tok R₁ [])
                (p₃ : Parser Tok R₂ xs) →
    ∀ n → p₁ ⊙ p₂ ↑ n ⊙ p₃ ⊑ p₁ ⊙ p₂ ⋆ ⊙ p₃
  upper-bound {R₁ = R₁} {fs = fs} {xs} _ _ _ n (∈p₁p₂ⁿ ⊛ ∈p₃)
    with drop-♭♯ xs ∈p₁p₂ⁿ
  ... | ∈p₁ ⊛ ∈p₂ⁿ =
    add-♭♯ xs (add-♭♯ [ List R₁ ∶ [] ] (drop-♭♯ ↑-n ∈p₁) ⊛
               add-♭♯ fs (Exactly.↑⊑⋆ n (drop-♭♯ fs ∈p₂ⁿ))) ⊛
    add-♭♯ (fs ⊛′ [ [] ]) (drop-♭♯ (fs ⊛′ ↑-n) ∈p₃)
    where ↑-n = ↑-initial [] n

  least-upper-bound : ∀ {Tok R₁ R₂ R₃ fs xs₃ xs}
                      (p₁ : Parser Tok (List R₁ → R₂ → R₃) fs)
                      (p₂ : Parser Tok R₁ [])
                      (p₃ : Parser Tok R₂ xs₃)
                      (p  : Parser Tok R₃ xs) →
    (∀ i → p₁ ⊙ p₂ ↑ i ⊙ p₃ ⊑ p) → p₁ ⊙ p₂ ⋆ ⊙ p₃ ⊑ p
  least-upper-bound
    {R₁ = R₁} {fs = fs} {xs₃} {xs} _ _ _ _ ub (∈p₁p₂⋆ ⊛ ∈p₃)
    with drop-♭♯ xs₃ ∈p₁p₂⋆
  ... | ∈p₁ ⊛ ∈p₂⋆ with Exactly.⋆⊑↑ (drop-♭♯ fs ∈p₂⋆)
  ... | (n , ∈p₂ⁿ) =
    ub n (add-♭♯ xs₃ (add-♭♯ ↑-n (drop-♭♯ [ List R₁ ∶ [] ] ∈p₁) ⊛
                      add-♭♯ fs ∈p₂ⁿ) ⊛
          add-♭♯ (fs ⊛′ ↑-n) (drop-♭♯ (fs ⊛′ [ List R₁ ∶ [] ]) ∈p₃))
    where ↑-n = ↑-initial [] n

  -- However, if we allow arbitrary argument parsers, then we cannot
  -- even prove the following (variant of a) Kleene algebra axiom.

  not-Kleene-algebra :
    (f : ∀ {Tok R xs} → Parser Tok R xs → List (List R)) →
    (_⋆′ : ∀ {Tok R xs} (p : Parser Tok R xs) →
           Parser Tok (List R) (f p)) →
    ¬ (∀ {Tok R xs} {p : Parser Tok R xs} →
       return [] ∣ _∷_ <$> p ⊙ (p ⋆′) ⊑ (p ⋆′))
  not-Kleene-algebra f _⋆′ fold =
    KleeneStar.unrestricted-incomplete tt f _⋆′ ⋆′-complete
    where
    ⋆′-complete : ∀ {xs ys s} {p : Parser ⊤ ⊤ ys} →
                  xs ∈[ p ]⋆· s → xs ∈ p ⋆′ · s
    ⋆′-complete                   []         = fold (∣ˡ return)
    ⋆′-complete {ys = ys} {p = p} (∈p ∷ ∈p⋆) =
      fold (∣ʳ [ [] ] (add-♭♯ (f p) (<$> ∈p) ⊛
                       add-♭♯ (List.map _∷_ ys) (⋆′-complete ∈p⋆)))

  -- This shows that the parser combinators do not form a Kleene
  -- algebra (interpreted liberally) using _⊙_ for composition, return
  -- for unit, etc. However, it should be straightforward to build a
  -- recogniser library, based on the parser combinators, which does
  -- satisfy the Kleene algebra axioms (see
  -- TotalRecognisers.LeftRecursion.KleeneAlgebra).
