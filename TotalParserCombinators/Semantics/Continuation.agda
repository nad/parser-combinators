------------------------------------------------------------------------
-- A semantics which uses continuation-passing style
------------------------------------------------------------------------

module TotalParserCombinators.Semantics.Continuation where

open import Algebra
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
import Data.List.Properties as ListProp
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡ using (bag) renaming (_≈[_]_ to _List-≈[_]_)
private
  module LM {Tok : Set} = Monoid (List.monoid Tok)

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

-- The statement x ⊕ s₂ ∈ p · s means that there is some s₁ such that
-- s ≡ s₁ ++ s₂ and x ∈ p · s₁. This variant of the semantics is
-- perhaps harder to understand, but sometimes easier to work with
-- (and it is proved to be language equivalent to the semantics in
-- TotalParserCombinators.Semantics).

infix 4 _⊕_∈_·_

data _⊕_∈_·_ {Tok} : ∀ {R xs} → R → List Tok →
                     Parser Tok R xs → List Tok → Set₁ where
  return   : ∀ {R} {x : R} {s} → x ⊕ s ∈ return x · s
  token    : ∀ {x s} → x ⊕ s ∈ token · x ∷ s
  ∣ˡ       : ∀ {R x xs₁ xs₂ s s₁}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₁ : x ⊕ s₁ ∈ p₁ · s) → x ⊕ s₁ ∈ p₁ ∣ p₂ · s
  ∣ʳ       : ∀ {R x xs₂ s s₁} xs₁
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₂ : x ⊕ s₁ ∈ p₂ · s) → x ⊕ s₁ ∈ p₁ ∣ p₂ · s
  <$>_     : ∀ {R₁ R₂ x s s₁ xs} {p : Parser Tok R₁ xs} {f : R₁ → R₂}
             (x∈p : x ⊕ s₁ ∈ p · s) → f x ⊕ s₁ ∈ f <$> p · s
  _⊛_      : ∀ {R₁ R₂ f x s s₁ s₂ fs xs}
               {p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs}
               {p₂ : ∞? (Parser Tok  R₁       xs) fs} →
             (f∈p₁ : f ⊕ s₁ ∈ ♭? p₁ · s)
             (x∈p₂ : x ⊕ s₂ ∈ ♭? p₂ · s₁) →
             f x ⊕ s₂ ∈ p₁ ⊛ p₂ · s
  _>>=_    : ∀ {R₁ R₂ x y s s₁ s₂ xs} {f : R₁ → List R₂}
               {p₁ : Parser Tok R₁ xs}
               {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs}
             (x∈p₁ : x ⊕ s₁ ∈ p₁ · s)
             (y∈p₂x : y ⊕ s₂ ∈ ♭? (p₂ x) · s₁) →
             y ⊕ s₂ ∈ p₁ >>= p₂ · s
  _>>=!_   : ∀ {R₁ R₂ x y s s₁ s₂ xs}
               {p₁ : ∞ (Parser Tok R₁ xs)}
               {p₂ : R₁ → ∞? (Parser Tok R₂ []) xs}
             (x∈p₁ : x ⊕ s₁ ∈ ♭ p₁ · s)
             (y∈p₂x : y ⊕ s₂ ∈ ♭? (p₂ x) · s₁) →
             y ⊕ s₂ ∈ p₁ >>=! p₂ · s
  nonempty : ∀ {R xs x y s₂} s₁ {p : Parser Tok R xs}
             (x∈p : y ⊕ s₂ ∈ p · x ∷ s₁ ++ s₂) →
             y ⊕ s₂ ∈ nonempty p · x ∷ s₁ ++ s₂
  cast     : ∀ {R xs₁ xs₂ x s₁ s₂} {xs₁≈xs₂ : xs₁ List-≈[ bag ] xs₂}
               {p : Parser Tok R xs₁}
             (x∈p : x ⊕ s₂ ∈ p · s₁) → x ⊕ s₂ ∈ cast xs₁≈xs₂ p · s₁

-- A simple cast lemma.

private

  cast∈′ : ∀ {Tok R xs} {p : Parser Tok R xs} {x s s′ s₁} →
           s ≡ s′ → x ⊕ s₁ ∈ p · s → x ⊕ s₁ ∈ p · s′
  cast∈′ refl x∈ = x∈

-- The definition is sound and complete with respect to the one in
-- TotalParserCombinators.Semantics.

sound′ : ∀ {Tok R xs x s₂ s} {p : Parser Tok R xs} →
         x ⊕ s₂ ∈ p · s → ∃ λ s₁ → s ≡ s₁ ++ s₂ × x ∈ p · s₁
sound′ return            = ([]    , refl , return)
sound′ {x = x} token     = ([ x ] , refl , token)
sound′ (∣ˡ x∈p₁)         = Prod.map id (Prod.map id ∣ˡ)        (sound′ x∈p₁)
sound′ (∣ʳ e₁ x∈p₁)      = Prod.map id (Prod.map id (∣ʳ e₁))   (sound′ x∈p₁)
sound′ (<$> x∈p)         = Prod.map id (Prod.map id <$>_) (sound′ x∈p)
sound′ (f∈p₁ ⊛ x∈p₂)     with sound′ f∈p₁ | sound′ x∈p₂
sound′ (f∈p₁ ⊛ x∈p₂)     | (s₁ , refl , f∈p₁′) | (s₂ , refl , x∈p₂′) =
  (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _) , f∈p₁′ ⊛ x∈p₂′)
sound′ (x∈p₁ >>=  y∈p₂x) with sound′ x∈p₁ | sound′ y∈p₂x
sound′ (x∈p₁ >>=  y∈p₂x) | (s₁ , refl , x∈p₁′) | (s₂ , refl , y∈p₂x′) =
  (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _) , x∈p₁′ >>= y∈p₂x′)
sound′ (x∈p₁ >>=! y∈p₂x) with sound′ x∈p₁ | sound′ y∈p₂x
sound′ (x∈p₁ >>=! y∈p₂x) | (s₁ , refl , x∈p₁′) | (s₂ , refl , y∈p₂x′) =
  (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _) , x∈p₁′ >>=! y∈p₂x′)
sound′ (nonempty s₁ x∈p) with sound′ x∈p
sound′ (nonempty s₁ x∈p) | (y ∷ s , eq , x∈p′) = (y ∷ s , eq , nonempty x∈p′)
sound′ (nonempty s₁ x∈p) | ([]    , eq , x∈p′)
  with ListProp.left-identity-unique (_ ∷ s₁) (sym eq)
sound′ (nonempty s₁ x∈p) | ([]    , eq , x∈p′) | ()
sound′ (cast x∈p)        = Prod.map id (Prod.map id cast) (sound′ x∈p)

sound : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
        x ⊕ [] ∈ p · s → x ∈ p · s
sound x∈p with sound′ x∈p
sound x∈p | (s , refl , x∈p′) with s ++ [] | Prod.proj₂ LM.identity s
sound x∈p | (s , refl , x∈p′) | .s | refl = x∈p′

extend : ∀ {Tok R xs x s s′ s″} {p : Parser Tok R xs} →
         x ⊕ s′ ∈ p · s → x ⊕ s′ ++ s″ ∈ p · s ++ s″
extend return            = return
extend token             = token
extend (∣ˡ x∈p₁)         = ∣ˡ    (extend x∈p₁)
extend (∣ʳ e₁ x∈p₂)      = ∣ʳ e₁ (extend x∈p₂)
extend (     <$> x∈p)    =             <$> extend x∈p
extend (f∈p₁ ⊛   x∈p₂)   = extend f∈p₁ ⊛   extend x∈p₂
extend (x∈p₁ >>=  y∈p₂x) = extend x∈p₁ >>=  extend y∈p₂x
extend (x∈p₁ >>=! y∈p₂x) = extend x∈p₁ >>=! extend y∈p₂x
extend (cast x∈p)        = cast (extend x∈p)
extend (nonempty s₁ x∈p) = cast₂ (nonempty s₁ (cast₁ (extend x∈p)))
  where
  lem   = LM.assoc (_ ∷ s₁) _ _
  cast₁ = cast∈′      lem
  cast₂ = cast∈′ (sym lem)

complete : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
           x ∈ p · s → x ⊕ [] ∈ p · s
complete return                 = return
complete token                  = token
complete (∣ˡ x∈p₁)              = ∣ˡ    (complete x∈p₁)
complete (∣ʳ e₁ x∈p₂)           = ∣ʳ e₁ (complete x∈p₂)
complete (     <$> x∈p)         =                        <$> complete x∈p
complete (f∈p₁ ⊛   x∈p₂)        = extend (complete f∈p₁) ⊛   complete x∈p₂
complete (x∈p₁ >>=  y∈p₂x)      = extend (complete x∈p₁) >>=  complete y∈p₂x
complete (x∈p₁ >>=! y∈p₂x)      = extend (complete x∈p₁) >>=! complete y∈p₂x
complete (cast x∈p)             = cast (complete x∈p)
complete (nonempty {s = s} x∈p) = cast₂ (nonempty s (cast₁ (complete x∈p)))
  where
  lem   = Prod.proj₂ LM.identity _
  cast₁ = cast∈′ (sym lem)
  cast₂ = cast∈′      lem

complete′ : ∀ {Tok R xs x s₂ s} {p : Parser Tok R xs} →
            (∃ λ s₁ → s ≡ s₁ ++ s₂ × x ∈ p · s₁) →
            x ⊕ s₂ ∈ p · s
complete′ (s₁ , refl , x∈p) = extend (complete x∈p)
