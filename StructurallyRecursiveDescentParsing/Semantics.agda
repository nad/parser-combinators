------------------------------------------------------------------------
-- Semantics of the parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Semantics where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.List as List
private
  module LM {Tok} = Monoid (List.monoid Tok)
import Data.Product as Prod
open import Data.Product1 as Prod1 renaming (∃₀₁ to ∃; map₀₁ to map)
open import Data.Function
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Type

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infix 4 _∈_·_

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
             {p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)}
           (x∈p₁ : x ∈ p₁ · s₁) (y∈p₂x : y ∈ ♭₁ (p₂ x) · s₂) →
           y ∈ p₁ !>>= p₂ · s₁ ++ s₂

------------------------------------------------------------------------
-- Some lemmas

-- A simple cast lemma.

cast : ∀ {Tok e R} {p : Parser Tok e R} {x s s′} →
       s ≡ s′ → x ∈ p · s → x ∈ p · s′
cast refl x∈ = x∈

-- Sanity check: The Bool index is true iff the empty string is
-- accepted.

does : ∀ {Tok R} (p : Parser Tok true R) → ∃ λ x → x ∈ p · []
does p = does′ p refl
  where
  does′ : ∀ {Tok e R}
          (p : Parser Tok e R) → e ≡ true → ∃ λ x → x ∈ p · []
  does′ (return x)          refl = (x , return)
  does′ (_∣_ {true}  p₁ p₂) refl = Prod1.map id ∣ˡ         (does p₁)
  does′ (_∣_ {false} p₁ p₂) refl = Prod1.map id (∣ʳ false) (does p₂)
  does′ (p₁ ?>>= p₂)        refl with does p₁
  does′ (p₁ ?>>= p₂)        refl | (x , x∈p₁·[]) =
    Prod1.map id (_?>>=_ x∈p₁·[]) (does (p₂ x))
  does′ fail         ()
  does′ token        ()
  does′ (p₁ !>>= p₂) ()

doesNot : ∀ {Tok R x} {p : Parser Tok false R} → x ∈ p · [] → ⊥
doesNot x∈p·[] = doesNot′ x∈p·[] refl refl
  where
  doesNot′ : ∀ {Tok R x e s} {p : Parser Tok e R} →
             x ∈ p · s → e ≡ false → s ≢ []
  doesNot′ (∣ˡ {e₁ = false} x∈p₁)        refl refl = doesNot x∈p₁
  doesNot′ (∣ʳ       false  x∈p₂)        refl refl = doesNot x∈p₂
  doesNot′ (_?>>=_ {s₁ = []} x∈p₁ y∈p₂x) refl refl = doesNot y∈p₂x
  doesNot′ (_!>>=_ {s₁ = []} x∈p₁ y∈p₂x) refl refl = doesNot x∈p₁

  doesNot′ return                    () _
  doesNot′ token                     _  ()
  doesNot′ (∣ˡ {e₁ = true} x∈p₁)     () _
  doesNot′ (∣ʳ       true  x∈p₂)     () _
  doesNot′ (_?>>=_ {s₁ = _ ∷ _} _ _) _  ()
  doesNot′ (_!>>=_ {s₁ = _ ∷ _} _ _) _  ()

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
             {p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)}
           (x∈p₁ : x ⊕ s₁ ∈ p₁ · s) (y∈p₂x : y ⊕ s₂ ∈ ♭₁ (p₂ x) · s₁) →
           y ⊕ s₂ ∈ p₁ !>>= p₂ · s

-- The definition is sound and complete with respect to the one above.

sound′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
         x ⊕ s₂ ∈ p · s → ∃ λ s₁ → Σ₀₁ (s ≡ s₁ ++ s₂) λ _ → x ∈ p · s₁
sound′ return            = ([]    , refl , return)
sound′ {x = x} token     = ([ x ] , refl , token)
sound′ (∣ˡ x∈p₁)         with sound′ x∈p₁
sound′ (∣ˡ x∈p₁)         | (s₁ , refl , x∈p₁′) = (s₁ , refl , ∣ˡ    x∈p₁′)
sound′ (∣ʳ e₁ x∈p₁)      with sound′ x∈p₁
sound′ (∣ʳ e₁ x∈p₁)      | (s₁ , refl , x∈p₁′) = (s₁ , refl , ∣ʳ e₁ x∈p₁′)
sound′ (x∈p₁ ?>>= y∈p₂x) with sound′ x∈p₁ | sound′ y∈p₂x
sound′ (x∈p₁ ?>>= y∈p₂x) | (s₁ , refl , x∈p₁′) | (s₂ , refl , y∈p₂x′) =
                           (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _)
                                     , x∈p₁′ ?>>= y∈p₂x′)
sound′ (x∈p₁ !>>= y∈p₂x) with sound′ x∈p₁ | sound′ y∈p₂x
sound′ (x∈p₁ !>>= y∈p₂x) | (s₁ , refl , x∈p₁′) | (s₂ , refl , y∈p₂x′) =
                           (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _)
                                     , x∈p₁′ !>>= y∈p₂x′)

sound : ∀ {Tok R e x s} {p : Parser Tok e R} →
        x ⊕ [] ∈ p · s → x ∈ p · s
sound x∈p with sound′ x∈p
sound x∈p | (s , refl , x∈p′) with s ++ [] | Prod.proj₂ LM.identity s
sound x∈p | (s , refl , x∈p′) | .s | refl = x∈p′

extend : ∀ {Tok R e x s s′ s″} {p : Parser Tok e R} →
         x ⊕ s′ ∈ p · s → x ⊕ s′ ++ s″ ∈ p · s ++ s″
extend return            = return
extend token             = token
extend (∣ˡ x∈p₁)         = ∣ˡ    (extend x∈p₁)
extend (∣ʳ e₁ x∈p₂)      = ∣ʳ e₁ (extend x∈p₂)
extend (x∈p₁ ?>>= y∈p₂x) = extend x∈p₁ ?>>= extend y∈p₂x
extend (x∈p₁ !>>= y∈p₂x) = extend x∈p₁ !>>= extend y∈p₂x

complete : ∀ {Tok R e x s} {p : Parser Tok e R} →
           x ∈ p · s → x ⊕ [] ∈ p · s
complete return            = return
complete token             = token
complete (∣ˡ x∈p₁)         = ∣ˡ    (complete x∈p₁)
complete (∣ʳ e₁ x∈p₂)      = ∣ʳ e₁ (complete x∈p₂)
complete (x∈p₁ ?>>= y∈p₂x) = extend (complete x∈p₁) ?>>=
                                     complete y∈p₂x
complete (x∈p₁ !>>= y∈p₂x) = extend (complete x∈p₁) !>>=
                                     complete y∈p₂x

complete′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
            (∃ λ s₁ → Σ₀₁ (s ≡ s₁ ++ s₂) λ _ → x ∈ p · s₁) →
            x ⊕ s₂ ∈ p · s
complete′ (s₁ , refl , x∈p) = extend (complete x∈p)
