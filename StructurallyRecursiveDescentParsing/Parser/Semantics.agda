------------------------------------------------------------------------
-- Semantics of the parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Parser.Semantics where

open import Algebra
import Algebra.Props.BooleanAlgebra as BAProp
open import Data.Bool
import Data.Bool.Properties as BoolProp
private
  module BCS = CommutativeSemiring BoolProp.commutativeSemiring-∨-∧
  module BA  = BAProp BoolProp.booleanAlgebra
open import Data.List as List
private module LM {Tok} = Monoid (List.monoid Tok)
import Data.List.Properties as ListProp
import Data.Product as Prod
open Prod using (_,_)
open import Data.Product1 as Prod1 renaming (∃₀₁ to ∃; map₀₁ to map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Function
open import Data.Empty
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.PropositionalEquality1 using (_≡₁_; refl)

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infixl 10 _>>=_
infix   4 _∈_·_

data _∈_·_ {Tok} : ∀ {R e} → R → Parser Tok e R → List Tok → Set1 where
  return : ∀ {R} {x : R} → x ∈ return x · []
  token  : ∀ {x} → x ∈ token · [ x ]
  ∣ˡ     : ∀ {R x e₁ e₂ s} {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₁ : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣ʳ     : ∀ {R x e₂ s} e₁ {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₂ : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  _>>=_  : ∀ {e₁ R₁ R₂ x y s₁ s₂} {e₂ : R₁ → Bool}
             {p₁ : Parser Tok e₁ R₁}
             {p₂ : (x : R₁) → ∞? e₁ (Parser Tok (e₂ x) R₂)} →
           (x∈p₁ : x ∈ p₁ · s₁) (y∈p₂x : y ∈ ♭? e₁ (p₂ x) · s₂) →
           y ∈ p₁ >>= p₂ · s₁ ++ s₂
  cast   : ∀ {e₁ e₂ R x s} {eq : e₁ ≡ e₂} {p : Parser Tok e₁ R} →
           (x∈p : x ∈ p · s) → x ∈ cast eq p · s

-- Equivalence of parsers (languages).

infix 4 _⊑_ _≈_

_⊑_ : ∀ {Tok e R} (p₁ p₂ : Parser Tok e R) → Set1
p₁ ⊑ p₂ = ∀ {x s} → x ∈ p₁ · s → x ∈ p₂ · s

_≈_ : ∀ {Tok e R} (p₁ p₂ : Parser Tok e R) → Set1
p₁ ≈ p₂ = Σ₁₁ (p₁ ⊑ p₂) λ _ → p₂ ⊑ p₁

------------------------------------------------------------------------
-- Some lemmas

-- A simple cast lemma.

cast∈ : ∀ {Tok e R} {p p′ : Parser Tok e R} {x x′ s s′} →
        x ≡ x′ → p ≡₁ p′ → s ≡ s′ → x ∈ p · s → x′ ∈ p′ · s′
cast∈ refl refl refl x∈ = x∈

mutual

  -- Sanity check: The initial set is correctly defined. Note that,
  -- although _∈_·_ depends indirectly on the definition of initial,
  -- this dependence is very weak.

  initial-complete : ∀ {Tok e R x} {p : Parser Tok e R} →
                     x ∈ p · [] → x ∈ initial p
  initial-complete x∈p = initial-complete′ x∈p refl
    where
    initial-complete′ : ∀ {Tok e R x s} {p : Parser Tok e R} →
                        x ∈ p · s → s ≡ [] → x ∈ initial p
    initial-complete′ return                               refl = here
    initial-complete′ (∣ˡ         x∈p₁)                    refl = ListProp.∈-++ˡ (initial-complete x∈p₁)
    initial-complete′ (∣ʳ e₁ {p₁} x∈p₂)                    refl = ListProp.∈-++ʳ (initial p₁) (initial-complete x∈p₂)
    initial-complete′ (_>>=_ {true}  {s₁ = []} x∈p₁ y∈p₂x) refl = ListProp.∈-concat (initial-complete y∈p₂x)
                                                                                    (ListProp.∈-map (initial-complete x∈p₁))
    initial-complete′ (cast x∈p)                           refl = initial-complete x∈p

    initial-complete′ (_>>=_ {false} {s₁ = []} x∈p₁ y∈p₂x) refl = ⊥-elim (doesNot x∈p₁)

    initial-complete′ token                    ()
    initial-complete′ (_>>=_ {s₁ = _ ∷ _} _ _) ()

  initial-sound : ∀ {Tok e R x} (p : Parser Tok e R) →
                  x ∈ initial p → x ∈ p · []
  initial-sound (return x)           here  = return
  initial-sound (p₁ ∣ p₂)            x∈fs  with ListProp.++-∈ (initial p₁) x∈fs
  initial-sound (p₁ ∣ p₂)            x∈fs  | inj₁ x∈fs₁ = ∣ˡ    (initial-sound p₁ x∈fs₁)
  initial-sound (_∣_ {e₁} p₁ p₂)     x∈fs  | inj₂ x∈fs₂ = ∣ʳ e₁ (initial-sound p₂ x∈fs₂)
  initial-sound (_>>=_ {true} p₁ p₂) y∈cfs
    with Prod.map id (Prod.map id (ListProp.map-∈ (initial p₁)))
           (ListProp.concat-∈ (List.map (λ x → initial (p₂ x)) (initial p₁))
                              y∈cfs)
  ... | (.(initial (p₂ x)) , y∈fs₂ , (x , x∈fs₁ , refl)) =
    initial-sound p₁ x∈fs₁ >>= initial-sound (p₂ x) y∈fs₂
  initial-sound (cast eq p)          x∈fs  = cast (initial-sound p x∈fs)

  initial-sound (return x)          (there ())
  initial-sound fail                ()
  initial-sound token               ()
  initial-sound (_>>=_ {false} _ _) ()

  -- Sanity check: The Bool index is true iff the empty string is
  -- accepted.

  does : ∀ {Tok R} (p : Parser Tok true R) → ∃ λ x → x ∈ p · []
  does p = does′ p refl
    where
    does′ : ∀ {Tok e R}
            (p : Parser Tok e R) → e ≡ true → ∃ λ x → x ∈ p · []
    does′ (return x)           refl = (x , return)
    does′ (_∣_ {true}  p₁ p₂)  refl = Prod1.map id ∣ˡ         (does p₁)
    does′ (_∣_ {false} p₁ p₂)  refl = Prod1.map id (∣ʳ false) (does p₂)
    does′ (_>>=_ {true} p₁ p₂) eq   with ListProp.any-∈ _ (initial p₁) eq
    does′ (_>>=_ {true} p₁ p₂) eq   | (x , x∈fs₁ , e₂x) with does′ (p₂ x) e₂x
    does′ (_>>=_ {true} p₁ p₂) eq   | (x , x∈fs₁ , e₂x) | (y , y∈p₂x) =
      (y , initial-sound p₁ x∈fs₁ >>= y∈p₂x)
    does′ (cast refl p)        refl = Prod1.map id cast (does p)

    does′ fail                ()
    does′ token               ()
    does′ (_>>=_ {false} _ _) ()

  doesNot : ∀ {Tok R x} {p : Parser Tok false R} → x ∈ p · [] → ⊥
  doesNot x∈p·[] = doesNot′ x∈p·[] refl refl
    where
    doesNot′ : ∀ {Tok R x e s} {p : Parser Tok e R} →
               x ∈ p · s → e ≡ false → s ≢ []
    doesNot′ (∣ˡ {e₁ = false} x∈p₁)              refl refl = doesNot x∈p₁
    doesNot′ (∣ʳ       false  x∈p₂)              refl refl = doesNot x∈p₂
    doesNot′ (_>>=_ {true} {s₁ = []} x∈p₁ y∈p₂x) eq   refl =
      doesNot′ y∈p₂x (BoolProp.¬-not
                        (contraposition
                           (ListProp.∈-any _ (initial-complete x∈p₁))
                           (BoolProp.not-¬ eq))) refl
    doesNot′ (_>>=_ {false} {s₁ = []} x∈p₁ y∈p₂x) refl refl = doesNot x∈p₁
    doesNot′ (cast {eq = refl} x∈p)               refl refl = doesNot x∈p

    doesNot′ return                   () _
    doesNot′ token                    _  ()
    doesNot′ (∣ˡ {e₁ = true} x∈p₁)    () _
    doesNot′ (∣ʳ       true  x∈p₂)    () _
    doesNot′ (_>>=_ {s₁ = _ ∷ _} _ _) _  ()

any-initial-true : ∀ {Tok R} (p : Parser Tok true R) {b} →
                   any (const b) (initial p) ≡ b
any-initial-true p {false} = BoolProp.¬-not $ λ any-false →
  (false ≢ true ∶ λ ()) $ Prod.proj₂ $ Prod.proj₂ $
    ListProp.any-∈ (const false) (initial p) any-false
any-initial-true p {true}  =
  ListProp.∈-any (const true)
                 (initial-complete (Prod1.proj₀₁₂ (does p)))
                 refl

any-initial-false : ∀ {Tok R} (p : Parser Tok false R) (e : R → Bool) →
                    any e (initial p) ≡ false
any-initial-false p e = BoolProp.¬-not $ λ any-e →
  doesNot (initial-sound p (Prod.proj₁ $ Prod.proj₂ $
                              ListProp.any-∈ e (initial p) any-e))

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
  _>>=_  : ∀ {e₁ R₁ R₂ x y s s₁ s₂} {e₂ : R₁ → Bool}
             {p₁ : Parser Tok e₁ R₁}
             {p₂ : (x : R₁) → ∞? e₁ (Parser Tok (e₂ x) R₂)} →
           (x∈p₁ : x ⊕ s₁ ∈ p₁ · s)
           (y∈p₂x : y ⊕ s₂ ∈ ♭? e₁ (p₂ x) · s₁) →
           y ⊕ s₂ ∈ p₁ >>= p₂ · s
  cast   : ∀ {e₁ e₂ R x s₁ s₂} {eq : e₁ ≡ e₂} {p : Parser Tok e₁ R} →
           (x∈p : x ⊕ s₂ ∈ p · s₁) → x ⊕ s₂ ∈ cast eq p · s₁

-- The definition is sound and complete with respect to the one above.

sound′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
         x ⊕ s₂ ∈ p · s → ∃ λ s₁ → Σ₀₁ (s ≡ s₁ ++ s₂) λ _ → x ∈ p · s₁
sound′ return           = ([]    , refl , return)
sound′ {x = x} token    = ([ x ] , refl , token)
sound′ (∣ˡ x∈p₁)        = Prod1.map id (Prod1.map id ∣ˡ)      (sound′ x∈p₁)
sound′ (∣ʳ e₁ x∈p₁)     = Prod1.map id (Prod1.map id (∣ʳ e₁)) (sound′ x∈p₁)
sound′ (x∈p₁ >>= y∈p₂x) with sound′ x∈p₁ | sound′ y∈p₂x
sound′ (x∈p₁ >>= y∈p₂x) | (s₁ , refl , x∈p₁′) | (s₂ , refl , y∈p₂x′) =
  (s₁ ++ s₂ , sym (LM.assoc s₁ s₂ _) , x∈p₁′ >>= y∈p₂x′)
sound′ (cast x∈p)       = Prod1.map id (Prod1.map id cast) (sound′ x∈p)

sound : ∀ {Tok R e x s} {p : Parser Tok e R} →
        x ⊕ [] ∈ p · s → x ∈ p · s
sound x∈p with sound′ x∈p
sound x∈p | (s , refl , x∈p′) with s ++ [] | Prod.proj₂ LM.identity s
sound x∈p | (s , refl , x∈p′) | .s | refl = x∈p′

extend : ∀ {Tok R e x s s′ s″} {p : Parser Tok e R} →
         x ⊕ s′ ∈ p · s → x ⊕ s′ ++ s″ ∈ p · s ++ s″
extend return           = return
extend token            = token
extend (∣ˡ x∈p₁)        = ∣ˡ    (extend x∈p₁)
extend (∣ʳ e₁ x∈p₂)     = ∣ʳ e₁ (extend x∈p₂)
extend (x∈p₁ >>= y∈p₂x) = extend x∈p₁ >>= extend y∈p₂x
extend (cast x∈p)       = cast (extend x∈p)

complete : ∀ {Tok R e x s} {p : Parser Tok e R} →
           x ∈ p · s → x ⊕ [] ∈ p · s
complete return           = return
complete token            = token
complete (∣ˡ x∈p₁)        = ∣ˡ    (complete x∈p₁)
complete (∣ʳ e₁ x∈p₂)     = ∣ʳ e₁ (complete x∈p₂)
complete (x∈p₁ >>= y∈p₂x) = extend (complete x∈p₁) >>= complete y∈p₂x
complete (cast x∈p)       = cast (complete x∈p)

complete′ : ∀ {Tok R e x s₂ s} {p : Parser Tok e R} →
            (∃ λ s₁ → Σ₀₁ (s ≡ s₁ ++ s₂) λ _ → x ∈ p · s₁) →
            x ⊕ s₂ ∈ p · s
complete′ (s₁ , refl , x∈p) = extend (complete x∈p)
