------------------------------------------------------------------------
-- Semantics of the parsers
------------------------------------------------------------------------

module TotalParserCombinators.Parser.Semantics where

open import Algebra
import Algebra.Props.BooleanAlgebra as BAProp
open import Coinduction
open import Data.Bool
import Data.Bool.Properties as BoolProp
private
  module BCS = CommutativeSemiring BoolProp.commutativeSemiring-∨-∧
  module BA  = BAProp BoolProp.booleanAlgebra
open import Data.List as List
import Data.List.Properties as ListProp
open import Data.List.Any
open Membership-≡
private module LM {Tok} = Monoid (List.monoid Tok)
open import Data.List.Any.Properties as AnyProp
open AnyProp.Membership-≡
open import Data.Product as Prod
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Function hiding (_∶_)
open import Data.Empty
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infix  60 <$>_
infixl 50 _⊛_
infixl 10 _>>=_ _>>=!_
infix   4 _∈_·_

data _∈_·_ {Tok} :
       ∀ {R xs} → R → Parser Tok R xs → List Tok → Set₁ where
  return   : ∀ {R} {x : R} → x ∈ return x · []
  token    : ∀ {x} → x ∈ token · [ x ]
  ∣ˡ       : ∀ {R x xs₁ xs₂ s}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₁ : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣ʳ       : ∀ {R x xs₂ s} xs₁
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₂ : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  <$>_     : ∀ {R₁ R₂ x s xs} {p : Parser Tok R₁ xs} {f : R₁ → R₂}
             (x∈p : x ∈ p · s) → f x ∈ f <$> p · s
  _⊛_      : ∀ {R₁ R₂ f x s₁ s₂ fs xs}
               {p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs}
               {p₂ : ∞? (Parser Tok  R₁       xs) fs} →
             (f∈p₁ : f ∈ ♭? p₁ · s₁)
             (x∈p₂ : x ∈ ♭? p₂ · s₂) →
             f x ∈ p₁ ⊛ p₂ · s₁ ++ s₂
  _>>=_    : ∀ {R₁ R₂ x y s₁ s₂ xs} {f : R₁ → List R₂}
               {p₁ : Parser Tok R₁ xs}
               {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs}
             (x∈p₁ : x ∈ p₁ · s₁)
             (y∈p₂x : y ∈ ♭? (p₂ x) · s₂) →
             y ∈ p₁ >>= p₂ · s₁ ++ s₂
  _>>=!_   : ∀ {R₁ R₂ x y s₁ s₂ xs}
               {p₁ : ∞ (Parser Tok R₁ xs)}
               {p₂ : R₁ → ∞? (Parser Tok R₂ []) xs}
             (x∈p₁ : x ∈ ♭ p₁ · s₁)
             (y∈p₂x : y ∈ ♭? (p₂ x) · s₂) →
             y ∈ p₁ >>=! p₂ · s₁ ++ s₂
  nonempty : ∀ {R xs x y s} {p : Parser Tok R xs}
             (x∈p : y ∈ p · x ∷ s) → y ∈ nonempty p · x ∷ s
  cast     : ∀ {R xs₁ xs₂ x s} {eq : xs₁ ≡ xs₂} {p : Parser Tok R xs₁}
             (x∈p : x ∈ p · s) → x ∈ cast eq p · s

-- Equivalence of parsers (languages).

infix 4 _⊑_ _≈_

_⊑_ : ∀ {Tok R xs} (p₁ p₂ : Parser Tok R xs) → Set₁
p₁ ⊑ p₂ = ∀ {x s} → x ∈ p₁ · s → x ∈ p₂ · s

_≈_ : ∀ {Tok R xs} (p₁ p₂ : Parser Tok R xs) → Set₁
p₁ ≈ p₂ = p₁ ⊑ p₂ × p₂ ⊑ p₁

------------------------------------------------------------------------
-- Some lemmas

-- A simple cast lemma.

cast∈ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′} →
        x ≡ x′ → p ≡ p′ → s ≡ s′ → x ∈ p · s → x′ ∈ p′ · s′
cast∈ refl refl refl x∈ = x∈

-- Sanity check: The initial set is correctly defined.

initial-complete : ∀ {Tok R xs x} {p : Parser Tok R xs} →
                   x ∈ p · [] → x ∈ xs
initial-complete x∈p = initial-complete′ x∈p refl
  where
  initial-complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
                      x ∈ p · s → s ≡ [] → x ∈ xs
  initial-complete′ return                                        refl = here refl
  initial-complete′ (∣ˡ     x∈p₁)                                 refl = ++⁺ˡ (initial-complete x∈p₁)
  initial-complete′ (∣ʳ xs₁ x∈p₂)                                 refl = ++⁺ʳ xs₁ (initial-complete x∈p₂)
  initial-complete′ (<$> x∈p)                                     refl = map-∈⁺ (initial-complete x∈p)
  initial-complete′ (_⊛_   {s₁ = []} {fs = fs}        f∈p₁ x∈p₂)  refl = >>=-∈⁺ (λ x → List.map (λ f → f x) fs)
                                                                                (initial-complete x∈p₂)
                                                                                (map-∈⁺ (initial-complete f∈p₁))
  initial-complete′ (_>>=_ {s₁ = []} {xs = _ ∷ _} {f} x∈p₁ y∈p₂x) refl = >>=-∈⁺ f (initial-complete x∈p₁)
                                                                                  (initial-complete y∈p₂x)
  initial-complete′ (cast {eq = refl} x∈p)                        refl = initial-complete x∈p

  initial-complete′ (_>>=_  {s₁ = []} {xs = []} x∈p₁ y∈p₂x) refl with initial-complete x∈p₁
  ... | ()
  initial-complete′ (_>>=!_ {s₁ = []}           x∈p₁ y∈p₂x) refl with initial-complete y∈p₂x
  ... | ()

  initial-complete′ token                     ()
  initial-complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
  initial-complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
  initial-complete′ (_>>=!_ {s₁ = _ ∷ _} _ _) ()
  initial-complete′ (nonempty _)              ()

initial-sound : ∀ {Tok R xs x} (p : Parser Tok R xs) →
                x ∈ xs → x ∈ p · []
initial-sound (return x)              (here refl) = return
initial-sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs with ++⁻ xs₁ x∈xs
... | inj₁ x∈xs₁ = ∣ˡ     (initial-sound p₁ x∈xs₁)
... | inj₂ x∈xs₂ = ∣ʳ xs₁ (initial-sound p₂ x∈xs₂)
initial-sound (_<$>_ {xs = xs} f p) x∈xs with map-∈⁻ xs x∈xs
... | (y , y∈xs , refl) = <$> initial-sound p y∈xs
initial-sound (_⊛_ {fs = fs} {x ∷ xs} ⟨ p₁ ⟩ p₂) y∈ys
  with Prod.map id (Prod.map id (map-∈⁻ fs)) $
         >>=-∈⁻ (λ x → List.map (λ f → f x) fs) (x ∷ xs) y∈ys
initial-sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟪ p₂ ⟫) y∈ys | (x′ , x′∈x∷xs , (f′ , ()    , refl))
initial-sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩) y∈ys | (x′ , x′∈x∷xs , (f′ , f′∈fs , refl)) =
  initial-sound p₁ f′∈fs ⊛ initial-sound p₂ x′∈x∷xs
initial-sound (_>>=_ {xs = zs} {f} p₁ p₂) y∈ys
  with >>=-∈⁻ f zs y∈ys
... | (x , x∈zs , y∈fx) =
  _>>=_ {f = f} (initial-sound p₁ x∈zs) (helper (p₂ x) x∈zs y∈fx)
  where
  helper : ∀ {Tok R₁ R₂ x y xs} {zs : List R₁}
           (p : ∞? (Parser Tok R₂ xs) zs) →
           x ∈ zs → y ∈ xs → y ∈ ♭? p · []
  helper ⟨ p ⟩ _  = initial-sound p
  helper ⟪ p ⟫ ()
initial-sound (cast refl p) x∈xs = cast (initial-sound p x∈xs)

initial-sound (return _)   (there ())
initial-sound fail         ()
initial-sound token        ()
initial-sound (⟪ _ ⟫ ⊛ _)  ()
initial-sound (_ >>=! _)   ()
initial-sound (nonempty _) ()

------------------------------------------------------------------------
-- A variant of the semantics

-- The statement x ⊕ s₂ ∈ p · s means that there is some s₁ such that
-- s ≡ s₁ ++ s₂ and x ∈ p · s₁. This variant of the semantics is
-- perhaps harder to understand, but sometimes easier to work with
-- (and it is proved equivalent to the semantics above).

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
  cast     : ∀ {R xs₁ xs₂ x s₁ s₂} {eq : xs₁ ≡ xs₂}
               {p : Parser Tok R xs₁}
             (x∈p : x ⊕ s₂ ∈ p · s₁) → x ⊕ s₂ ∈ cast eq p · s₁

-- A simple cast lemma.

private

  cast∈′ : ∀ {Tok R xs} {p : Parser Tok R xs} {x s s′ s₁} →
           s ≡ s′ → x ⊕ s₁ ∈ p · s → x ⊕ s₁ ∈ p · s′
  cast∈′ refl x∈ = x∈

-- The definition is sound and complete with respect to the one above.

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