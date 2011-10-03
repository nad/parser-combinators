------------------------------------------------------------------------
-- Semantics of the parsers
------------------------------------------------------------------------

module TotalParserCombinators.Semantics where

open import Coinduction
open import Data.List hiding (drop)
import Data.List.Any as Any
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; module Equivalence)
open import Function.Inverse using (_↔_; module Inverse)
open import Function.Related as Related using (Related)
open import Level
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open Any.Membership-≡ using (bag) renaming (_∼[_]_ to _List-∼[_]_)

open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infix  60 <$>_
infixl 50 _⊛_   [_-_]_⊛_
infixl 10 _>>=_ [_-_]_>>=_
infix   4 _∈_·_

data _∈_·_ {Tok} :
       ∀ {R xs} → R → Parser Tok R xs → List Tok → Set₁ where
  return   : ∀ {R} {x : R} → x ∈ return x · []
  token    : ∀ {x} → x ∈ token · [ x ]
  ∣-left   : ∀ {R x xs₁ xs₂ s}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₁ : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣-right  : ∀ {R x xs₂ s} xs₁
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₂ : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  <$>_     : ∀ {R₁ R₂ x s xs} {p : Parser Tok R₁ xs} {f : R₁ → R₂}
             (x∈p : x ∈ p · s) → f x ∈ f <$> p · s
  _⊛_      : ∀ {R₁ R₂ f x s₁ s₂ fs xs}
               {p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)}
               {p₂ : ∞⟨ fs ⟩Parser Tok  R₁       (flatten xs)} →
             (f∈p₁ : f ∈ ♭? p₁ · s₁)
             (x∈p₂ : x ∈ ♭? p₂ · s₂) →
             f x ∈ p₁ ⊛ p₂ · s₁ ++ s₂
  _>>=_    : ∀ {R₁ R₂ x y s₁ s₂ xs} {f : Maybe (R₁ → List R₂)}
               {p₁ : ∞⟨ f ⟩Parser Tok R₁ (flatten xs)}
               {p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂ (apply f x)}
             (x∈p₁ : x ∈ ♭? p₁ · s₁)
             (y∈p₂x : y ∈ ♭? (p₂ x) · s₂) →
             y ∈ p₁ >>= p₂ · s₁ ++ s₂
  nonempty : ∀ {R xs x y s} {p : Parser Tok R xs}
             (x∈p : y ∈ p · x ∷ s) → y ∈ nonempty p · x ∷ s
  cast     : ∀ {R xs₁ xs₂ x s}
               {xs₁≈xs₂ : xs₁ List-∼[ bag ] xs₂} {p : Parser Tok R xs₁}
             (x∈p : x ∈ p · s) → x ∈ cast xs₁≈xs₂ p · s

-- Some variants with fewer implicit arguments. (The arguments xs and
-- fs can usually not be inferred, but I do not want to mention them
-- in the paper, so I have made them implicit in the definition
-- above.)

[_-_]_⊛_ : ∀ {Tok R₁ R₂ f x s₁ s₂} xs fs
             {p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)}
             {p₂ : ∞⟨ fs ⟩Parser Tok  R₁       (flatten xs)} →
           f ∈ ♭? p₁ · s₁ → x ∈ ♭? p₂ · s₂ → f x ∈ p₁ ⊛ p₂ · s₁ ++ s₂
[ xs - fs ] f∈p₁ ⊛ x∈p₂ = _⊛_ {fs = fs} {xs = xs} f∈p₁ x∈p₂

[_-_]_>>=_ : ∀ {Tok R₁ R₂ x y s₁ s₂} (f : Maybe (R₁ → List R₂)) xs
               {p₁ : ∞⟨ f ⟩Parser Tok R₁ (flatten xs)}
               {p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂ (apply f x)} →
             x ∈ ♭? p₁ · s₁ → y ∈ ♭? (p₂ x) · s₂ →
             y ∈ p₁ >>= p₂ · s₁ ++ s₂
[ f - xs ] x∈p₁ >>= y∈p₂x = _>>=_ {xs = xs} {f = f} x∈p₁ y∈p₂x

------------------------------------------------------------------------
-- Parser and language equivalence

infix 4 _∼[_]_ _≈_ _≅_ _≲_

-- There are two kinds of equivalences. Parser equivalences are
-- stronger, and correspond to bag equality. Language equivalences are
-- weaker, and correspond to set equality.

open Any.Membership-≡ public
  using (Kind)
  renaming ( bag      to parser
           ; set      to language
           ; subbag   to subparser
           ; subset   to sublanguage
           ; superbag to superparser
           ; superset to superlanguage
           )

-- General definition of equivalence between parsers. (Note that this
-- definition also gives access to some ordering relations.)

_∼[_]_ : ∀ {Tok R xs₁ xs₂} →
         Parser Tok R xs₁ → Kind → Parser Tok R xs₂ → Set₁
p₁ ∼[ k ] p₂ = ∀ {x s} → Related k (x ∈ p₁ · s) (x ∈ p₂ · s)

-- Language equivalence. (Corresponds to set equality.)

_≈_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≈ p₂ = p₁ ∼[ language ] p₂

-- Parser equivalence. (Corresponds to bag equality.)

_≅_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≅ p₂ = p₁ ∼[ parser ] p₂

-- p₁ ≲ p₂ means that the language defined by p₂ contains all the
-- string/result pairs contained in the language defined by p₁.

_≲_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≲ p₂ = p₁ ∼[ sublanguage ] p₂

-- p₁ ≈ p₂ iff both p₁ ≲ p₂ and p₂ ≲ p₁.

≈⇔≲≳ : ∀ {Tok R xs₁ xs₂}
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≈ p₂ ⇔ (p₁ ≲ p₂ × p₂ ≲ p₁)
≈⇔≲≳ = Eq.equivalence
  (λ p₁≈p₂  →
     ((λ {x s} → _⟨$⟩_ (Equivalence.to   (p₁≈p₂ {x = x} {s = s})))
     , λ {x s} → _⟨$⟩_ (Equivalence.from (p₁≈p₂ {x = x} {s = s}))))
  (λ p₁≲≳p₂ → λ {x s} → Eq.equivalence (proj₁ p₁≲≳p₂ {s = s})
                                       (proj₂ p₁≲≳p₂ {s = s}))

-- Parser equivalence implies language equivalence.

≅⇒≈ : ∀ {Tok R xs₁ xs₂}
        {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
      p₁ ≅ p₂ → p₁ ≈ p₂
≅⇒≈ p₁≅p₂ = Related.↔⇒ p₁≅p₂

-- Language equivalence does not (in general) imply parser
-- equivalence.

¬≈⇒≅ : ¬ (∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → p₁ ≅ p₂)
¬≈⇒≅ hyp with Inverse.injective p₁≅p₂
                {∣-left return} {∣-right [ tt ] return} (lemma _ _)
  where
  p₁ : Parser ⊤ ⊤ _
  p₁ = return tt ∣ return tt

  p₂ : Parser ⊤ ⊤ _
  p₂ = return tt

  p₁≲p₂ : p₁ ≲ p₂
  p₁≲p₂ (∣-left     return) = return
  p₁≲p₂ (∣-right ._ return) = return

  p₁≅p₂ : p₁ ≅ p₂
  p₁≅p₂ = hyp $ Eq.equivalence p₁≲p₂ ∣-left

  lemma : ∀ {x s} (x∈₁ x∈₂ : x ∈ p₂ · s) → x∈₁ ≡ x∈₂
  lemma return return = P.refl

... | ()

------------------------------------------------------------------------
-- A simple cast lemma

cast∈ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′} →
        x ≡ x′ → p ≡ p′ → s ≡ s′ → x ∈ p · s → x′ ∈ p′ · s′
cast∈ P.refl P.refl P.refl x∈ = x∈
