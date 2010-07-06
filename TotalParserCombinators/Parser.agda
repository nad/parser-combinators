------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module TotalParserCombinators.Parser where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
open import Data.Maybe
import Data.List.Any as Any
import Data.List.Properties as ListProp
open import Data.Product using (proj₂)
open import Function
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _⊛_    to _⊛′_
           ; _>>=_  to _>>=′_
           )

------------------------------------------------------------------------
-- Helper functions

-- maybeToList m f is equivalent to List.fromMaybe m >>=′ f, but
-- behaves better: maybeToList (just x) f evaluates to f x rather than
-- f x ++ []. The definitions of p and p′ below would have contained
-- unsolved meta-variables if maybeToList had been defined using
-- _>>=′_ as above.

maybeToList : {A B : Set} → Maybe A → (A → List B) → List B
maybeToList m f = maybe f [] m

-- Flattening for potential lists.

flatten : {A : Set} → Maybe (List A) → List A
flatten mxs = maybeToList mxs id

-- fs ⊛flatten mxs is a variant of fs ⊛′ flatten mxs, with the
-- property that fs ⊛flatten nothing evaluates to [].

_⊛flatten_ : {A B : Set} → List (A → B) → Maybe (List A) → List B
fs ⊛flatten mxs = maybeToList mxs (λ xs → fs ⊛′ xs)

-- Applies the function to the value, returning the empty list if
-- there is no function.

app : {A B : Set} → Maybe (A → List B) → A → List B
app mf x = maybeToList mf (λ f → f x)

-- xs >>=app mf is a variant of xs >>=′ app mf, with the property that
-- xs >>=app nothing evaluates to [].

_>>=app_ : {A B : Set} → List A → Maybe (A → List B) → List B
xs >>=app mf = maybeToList mf (λ f → xs >>=′ f)

-- Verification of some claims made above.

private

  claim₁ : {A B : Set} (m : Maybe A) (f : A → List B) →
           maybeToList m f ≡ (List.fromMaybe m >>=′ f)
  claim₁ nothing  f = refl
  claim₁ (just x) f =
    sym $ proj₂ (Monoid.identity $ List.monoid _) (f x)

  claim₂ : {A B : Set} (fs : List (A → B)) (mxs : Maybe (List A)) →
           fs ⊛flatten mxs ≡ fs ⊛′ flatten mxs
  claim₂ fs nothing   = sym $ ListProp.Monad.right-zero fs
  claim₂ fs (just xs) = refl

  claim₃ : {A B : Set} (fs : List (A → B)) →
           fs ⊛flatten nothing ≡ []
  claim₃ fs = refl

  claim₄ : {A B : Set} (xs : List A) (mf : Maybe (A → List B)) →
           xs >>=app mf ≡ (xs >>=′ app mf)
  claim₄ xs nothing  = sym $ ListProp.Monad.right-zero xs
  claim₄ xs (just f) = refl

  claim₅ : {A B : Set} (xs : List A) →
           xs >>=app nothing ≡ (List B ∶ [])
  claim₅ xs = refl

------------------------------------------------------------------------
-- Parsers

infixl 50 _⊛_ _<$>_ _⊛flatten_
infixl 10 _>>=_ _>>=app_
infixl  5 _∣_

-- The list index is the "initial bag"; it contains the results which
-- can be emitted without consuming any input. For
--   p : Parser Tok R xs
-- we have
--   x ∈ xs  iff  x ∈ p · []
-- (see TotalParserCombinators.InitialBag).

mutual

  data Parser (Tok : Set) : (R : Set) → List R → Set₁ where
    return   : ∀ {R} (x : R) → Parser Tok R (return′ x)
    fail     : ∀ {R} → Parser Tok R fail′
    token    : Parser Tok Tok fail′
    _∣_      : ∀ {R xs₁ xs₂}
               (p₁ : Parser Tok R  xs₁       )
               (p₂ : Parser Tok R         xs₂) →
                     Parser Tok R (xs₁ ∣′ xs₂)
    _<$>_    : ∀ {R₁ R₂ xs}
               (f : R₁ → R₂)
               (p : Parser Tok R₁        xs) →
                    Parser Tok R₂ (map f xs)
    _⊛_      : ∀ {R₁ R₂ fs xs}
               (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)            )
               (p₂ : ∞⟨ fs ⟩Parser Tok  R₁                   (flatten xs)) →
                            Parser Tok       R₂  (flatten fs ⊛flatten xs)
    _>>=_    : ∀ {R₁ R₂ xs} {f : Maybe (R₁ → List R₂)}
               (p₁ :            ∞⟨ f  ⟩Parser Tok R₁ (flatten xs)           )
               (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂               (app f x)) →
                                       Parser Tok R₂ (flatten xs >>=app f)
    nonempty : ∀ {R xs} (p : Parser Tok R xs) → Parser Tok R []
    cast     : ∀ {R xs₁ xs₂} (xs₁≈xs₂ : xs₁ ≈[ bag ] xs₂)
               (p : Parser Tok R xs₁) → Parser Tok R xs₂

  ∞⟨_⟩Parser : {R₂ : Set} → Maybe R₂ → Set → (R₁ : Set) → List R₁ → Set₁
  ∞⟨ nothing ⟩Parser Tok R₁ xs = ∞ (Parser Tok R₁ xs)
  ∞⟨ just _  ⟩Parser Tok R₁ xs =    Parser Tok R₁ xs

-- Note that, with the definition above, a sequenced parser is
-- /allowed/ to be delayed if the "other" parser is not nullable, but
-- it does not have to be.

-- Note also that it would be safe to make the first argument of _>>=_
-- coinductive if app f x ≡_[] for all x in xs. I suspect that this
-- criterion would be awkward to work with, though. Instead I only
-- allow the argument to be coinductive if f ≡ nothing.

------------------------------------------------------------------------
-- Examples

private

  -- Note that these parsers can be both left and right recursive:

  leftRight : ∀ {R Tok} → Parser Tok R _
  leftRight {R} = ♯ (const <$> leftRight) ⊛ ♯ leftRight {R}

  leftRight′ : ∀ {R Tok} → Parser Tok R _
  leftRight′ {R} = ♯ leftRight′ {R} >>= λ _ → ♯ leftRight′

  -- More examples, included to ensure that all implicit arguments are
  -- inferred automatically.

  p : {Tok R : Set} → Parser Tok R _
  p = token >>= λ _ → ♯ p

  p′ : {Tok : Set} → Parser Tok Tok _
  p′ = ♯ p′ >>= λ _ → token

------------------------------------------------------------------------
-- Helper functions related to ∞⟨_⟩Parser

-- Forces if necessary.

♭? : ∀ {Tok R₁ R₂} {m : Maybe R₂} {xs} →
     ∞⟨ m ⟩Parser Tok R₁ xs → Parser Tok R₁ xs
♭? {m = nothing} = ♭
♭? {m = just _}  = id

-- Is the argument parser delayed? If the result is nothing, then it
-- is.

delayed? : ∀ {Tok R R′ xs} {m : Maybe R′} →
           ∞⟨ m ⟩Parser Tok R xs → Maybe R′
delayed? {m = m} _ = m

delayed?′ : ∀ {Tok R₁ R₂ R′ : Set} {m : Maybe R′} {f : R₁ → List R₂} →
            ((x : R₁) → ∞⟨ m ⟩Parser Tok R₂ (f x)) → Maybe R′
delayed?′ {m = m} _ = m

-- Short synonyms for just and nothing. ◌ stands for "delayed" (think
-- "not here") and ○ for "not delayed".

◌ : {R : Set} → Maybe R
◌ = nothing

○ : {R : Set} {x : R} → Maybe R
○ {x = x} = just x
