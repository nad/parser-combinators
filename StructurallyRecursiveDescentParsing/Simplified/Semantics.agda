------------------------------------------------------------------------
-- Semantics of the simplified parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simplified.Semantics where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.List as List
private
  module LM {Tok : Set} = Monoid (List.monoid Tok)
open import Data.Product as Prod
open import Function
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import StructurallyRecursiveDescentParsing.Simplified
open import TotalParserCombinators.Parser using (○; ◌)
open import TotalParserCombinators.Semantics as Semantics
  using ([_-_]_>>=_) renaming (_∈_·_ to _∈′_·_)
open Semantics._∈_·_

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infixl 10 _?>>=_ _!>>=_
infix   4 _∈_·_

data _∈_·_ {Tok} : ∀ {R e} → R → Parser Tok e R → List Tok → Set1 where
  return : ∀ {R} {x : R} → x ∈ return x · []
  token  : ∀ {x} → x ∈ token · [ x ]
  ∣ˡ     : ∀ {R x e₁ e₂ s} {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₁ : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣ʳ     : ∀ {R x e₂ s} e₁ {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₂ : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  _?>>=_ : ∀ {R₁ R₂ x y e₂ s₁ s₂}
             {p₁ : Parser Tok true R₁} {p₂ : R₁ → Parser Tok e₂ R₂}
           (x∈p₁ : x ∈ p₁ · s₁) (y∈p₂x : y ∈ p₂ x · s₂) →
           y ∈ p₁ ?>>= p₂ · s₁ ++ s₂
  _!>>=_ : ∀ {R₁ R₂ x y} {e₂ : R₁ → Bool} {s₁ s₂}
             {p₁ : Parser Tok false R₁}
             {p₂ : (x : R₁) → ∞ (Parser Tok (e₂ x) R₂)}
           (x∈p₁ : x ∈ p₁ · s₁) (y∈p₂x : y ∈ ♭ (p₂ x) · s₂) →
           y ∈ p₁ !>>= p₂ · s₁ ++ s₂

------------------------------------------------------------------------
-- _∈_·_ is correct with respect to _∈′_·_

sound : ∀ {Tok e R} {p : Parser Tok e R} {x s} →
        x ∈ p · s → x ∈′ ⟦ p ⟧ · s
sound return              = return
sound token               = token
sound (∣ˡ x∈p₁)           = cast (∣-left               (sound x∈p₁))
sound (∣ʳ _ {p₁} x∈p₂)    = cast (∣-right (initial p₁) (sound x∈p₂))
sound (_?>>=_ {p₂ = p₂}
              x∈p₁ y∈p₂x) = cast ([_-_]_>>=_ ○ ○ {p₂ = λ x → ⟦ p₂ x ⟧}
                                             (sound x∈p₁) (sound y∈p₂x))
sound (x∈p₁ !>>= y∈p₂x)   = [ ○ - ◌ ] sound x∈p₁ >>= sound y∈p₂x

complete : ∀ {Tok e R} (p : Parser Tok e R) {x s} →
           x ∈′ ⟦ p ⟧ · s → x ∈ p · s
complete (return x)       return                   = return
complete fail             ()
complete token            token                    = token
complete (p₁ ∣ p₂)        (cast (∣-left     x∈p₁)) = ∣ˡ    (complete p₁ x∈p₁)
complete (_∣_ {e₁} p₁ p₂) (cast (∣-right ._ x∈p₂)) = ∣ʳ e₁ (complete p₂ x∈p₂)
complete (p₁ ?>>= p₂)     (cast (x∈p₁ >>= y∈p₂x))  = complete p₁ x∈p₁ ?>>= complete    (p₂ _)  y∈p₂x
complete (p₁ !>>= p₂)           (x∈p₁ >>= y∈p₂x)   = complete p₁ x∈p₁ !>>= complete (♭ (p₂ _)) y∈p₂x

------------------------------------------------------------------------
-- A lemma

-- A simple cast lemma.

cast∈ : ∀ {Tok e R} {p p′ : Parser Tok e R} {x x′ s s′} →
        x ≡ x′ → p ≡ p′ → s ≡ s′ → x ∈ p · s → x′ ∈ p′ · s′
cast∈ P.refl P.refl P.refl x∈ = x∈

------------------------------------------------------------------------
-- A variant of the semantics

-- The statement x ⊕ s₂ ∈ p · s means that there is some s₁ such that
-- s ≡ s₁ ++ s₂ and x ∈ p · s₁. This variant of the semantics is
-- perhaps harder to understand, but sometimes easier to work with
-- (and it is proved equivalent to the semantics above).

infix 4 _⊕_∈_·_

data _⊕_∈_·_ {Tok} : ∀ {R e} → R → List Tok →
                     Parser Tok e R → List Tok → Set1 where
  return : ∀ {R} {x : R} {s} → x ⊕ s ∈ return x · s
  token  : ∀ {x s} → x ⊕ s ∈ token · x ∷ s
  ∣ˡ     : ∀ {R x e₁ e₂ s s₁}
             {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₁ : x ⊕ s₁ ∈ p₁ · s) → x ⊕ s₁ ∈ p₁ ∣ p₂ · s
  ∣ʳ     : ∀ {R x e₂ s s₁} e₁
             {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₂ : x ⊕ s₁ ∈ p₂ · s) → x ⊕ s₁ ∈ p₁ ∣ p₂ · s
  _?>>=_ : ∀ {R₁ R₂ x y e₂ s s₁ s₂}
             {p₁ : Parser Tok true R₁} {p₂ : R₁ → Parser Tok e₂ R₂}
           (x∈p₁ : x ⊕ s₁ ∈ p₁ · s) (y∈p₂x : y ⊕ s₂ ∈ p₂ x · s₁) →
           y ⊕ s₂ ∈ p₁ ?>>= p₂ · s
  _!>>=_ : ∀ {R₁ R₂ x y} {e₂ : R₁ → Bool} {s s₁ s₂}
             {p₁ : Parser Tok false R₁}
             {p₂ : (x : R₁) → ∞ (Parser Tok (e₂ x) R₂)}
           (x∈p₁ : x ⊕ s₁ ∈ p₁ · s) (y∈p₂x : y ⊕ s₂ ∈ ♭ (p₂ x) · s₁) →
           y ⊕ s₂ ∈ p₁ !>>= p₂ · s

-- The definition is sound and complete with respect to the one above.

⊕-sound′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
           x ⊕ s₂ ∈ p · s → ∃ λ s₁ → (s ≡ s₁ ++ s₂) × (x ∈ p · s₁)
⊕-sound′ return            = ([]    , P.refl , return)
⊕-sound′ {x = x} token     = ([ x ] , P.refl , token)
⊕-sound′ (∣ˡ x∈p₁)         with ⊕-sound′ x∈p₁
⊕-sound′ (∣ˡ x∈p₁)         | (s₁ , P.refl , x∈p₁′) = (s₁ , P.refl , ∣ˡ    x∈p₁′)
⊕-sound′ (∣ʳ e₁ x∈p₁)      with ⊕-sound′ x∈p₁
⊕-sound′ (∣ʳ e₁ x∈p₁)      | (s₁ , P.refl , x∈p₁′) = (s₁ , P.refl , ∣ʳ e₁ x∈p₁′)
⊕-sound′ (x∈p₁ ?>>= y∈p₂x) with ⊕-sound′ x∈p₁ | ⊕-sound′ y∈p₂x
⊕-sound′ (x∈p₁ ?>>= y∈p₂x) | (s₁ , P.refl , x∈p₁′) | (s₂ , P.refl , y∈p₂x′) =
                             (s₁ ++ s₂ , P.sym (LM.assoc s₁ s₂ _)
                                       , x∈p₁′ ?>>= y∈p₂x′)
⊕-sound′ (x∈p₁ !>>= y∈p₂x) with ⊕-sound′ x∈p₁ | ⊕-sound′ y∈p₂x
⊕-sound′ (x∈p₁ !>>= y∈p₂x) | (s₁ , P.refl , x∈p₁′) | (s₂ , P.refl , y∈p₂x′) =
                             (s₁ ++ s₂ , P.sym (LM.assoc s₁ s₂ _)
                                       , x∈p₁′ !>>= y∈p₂x′)

⊕-sound : ∀ {Tok R e x s} {p : Parser Tok e R} →
          x ⊕ [] ∈ p · s → x ∈ p · s
⊕-sound x∈p with ⊕-sound′ x∈p
⊕-sound x∈p | (s , P.refl , x∈p′) with s ++ [] | proj₂ LM.identity s
⊕-sound x∈p | (s , P.refl , x∈p′) | .s | P.refl = x∈p′

extend : ∀ {Tok R e x s s′ s″} {p : Parser Tok e R} →
         x ⊕ s′ ∈ p · s → x ⊕ s′ ++ s″ ∈ p · s ++ s″
extend return            = return
extend token             = token
extend (∣ˡ x∈p₁)         = ∣ˡ    (extend x∈p₁)
extend (∣ʳ e₁ x∈p₂)      = ∣ʳ e₁ (extend x∈p₂)
extend (x∈p₁ ?>>= y∈p₂x) = extend x∈p₁ ?>>= extend y∈p₂x
extend (x∈p₁ !>>= y∈p₂x) = extend x∈p₁ !>>= extend y∈p₂x

⊕-complete : ∀ {Tok R e x s} {p : Parser Tok e R} →
             x ∈ p · s → x ⊕ [] ∈ p · s
⊕-complete return            = return
⊕-complete token             = token
⊕-complete (∣ˡ x∈p₁)         = ∣ˡ    (⊕-complete x∈p₁)
⊕-complete (∣ʳ e₁ x∈p₂)      = ∣ʳ e₁ (⊕-complete x∈p₂)
⊕-complete (x∈p₁ ?>>= y∈p₂x) = extend (⊕-complete x∈p₁) ?>>=
                                       ⊕-complete y∈p₂x
⊕-complete (x∈p₁ !>>= y∈p₂x) = extend (⊕-complete x∈p₁) !>>=
                                       ⊕-complete y∈p₂x

⊕-complete′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
              (∃ λ s₁ → s ≡ s₁ ++ s₂ × x ∈ p · s₁) →
              x ⊕ s₂ ∈ p · s
⊕-complete′ (s₁ , P.refl , x∈p) = extend (⊕-complete x∈p)
