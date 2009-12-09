------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

-- This module also provides examples of parsers for which the indices
-- cannot be inferred.

module StructurallyRecursiveDescentParsing.Lib where

open import StructurallyRecursiveDescentParsing.Grammar
open import StructurallyRecursiveDescentParsing.Index

open import Data.Nat hiding (_≟_)
open import Data.Vec as Vec using (Vec;  []; _∷_)
open import Data.List using (List; []; _∷_; foldr; foldl; reverse)
open import Data.Product
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Function
open import Data.Maybe
open import Data.Unit using (⊤)
import Data.Char as Char
open Char using (Char; _==_)
open import Coinduction
open import Algebra
import Data.Bool.Properties as Bool
private
  module BCS = CommutativeSemiring Bool.commutativeSemiring-∨-∧
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

------------------------------------------------------------------------
-- Some important derived combinators

infixl 10 _>>=_

_>>=_ : ∀ {NT Tok e₁ c₁ i₂ R₁ R₂} → let i₁ = e₁ ◇ c₁ in
        Parser NT Tok i₁ R₁ →
        (R₁ → Parser NT Tok i₂ R₂) →
        Parser NT Tok (i₁ · i₂) R₂
_>>=_ {e₁ = true } p₁ p₂ = p₁ ?>>= p₂
_>>=_ {e₁ = false} p₁ p₂ = p₁ !>>= λ x → ♯ p₂ x

cast : ∀ {NT Tok e₁ e₂ c₁ c₂ R} →
       e₁ ≡ e₂ → c₁ ≡ c₂ →
       Parser NT Tok (e₁ ◇ c₁) R → Parser NT Tok (e₂ ◇ c₂) R
cast refl refl p = p

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _⊛!_ _<⊛_ _⊛>_ _<$>_ _<$_ _⊗_ _⊗!_

_⊛_ : ∀ {NT Tok i₁ i₂ R₁ R₂} →
      Parser NT Tok i₁ (R₁ → R₂) →
      Parser NT Tok i₂ R₁ →
      Parser NT Tok _  R₂
p₁ ⊛ p₂ = p₁ >>= λ f → p₂ >>= λ x → return (f x)

-- A variant: If the second parser does not accept the empty string,
-- then neither does the combination. (This is immediate for the first
-- parser, but for the second one a small lemma is needed, hence this
-- variant.)

_⊛!_ : ∀ {NT Tok i₁ c₂ R₁ R₂} →
       Parser NT Tok i₁ (R₁ → R₂) →
       Parser NT Tok (false ◇ c₂) R₁ →
       Parser NT Tok (false ◇ _)  R₂
_⊛!_ {i₁ = i₁} p₁ p₂ = cast (BCS.*-comm (empty i₁) false) refl
                            (p₁ ⊛ p₂)

_<$>_ : ∀ {NT Tok i R₁ R₂} →
        (R₁ → R₂) →
        Parser NT Tok i R₁ →
        Parser NT Tok _ R₂
f <$> p = return f ⊛ p

_<⊛_ : ∀ {NT Tok i₁ i₂ R₁ R₂} →
       Parser NT Tok i₁ R₁ →
       Parser NT Tok i₂ R₂ →
       Parser NT Tok _ R₁
p₁ <⊛ p₂ = const <$> p₁ ⊛ p₂

_⊛>_ : ∀ {NT Tok i₁ i₂ R₁ R₂} →
       Parser NT Tok i₁ R₁ →
       Parser NT Tok i₂ R₂ →
       Parser NT Tok _ R₂
p₁ ⊛> p₂ = flip const <$> p₁ ⊛ p₂

_<$_ : ∀ {NT Tok i R₁ R₂} →
       R₁ →
       Parser NT Tok i R₂ →
       Parser NT Tok _ R₁
x <$ p = const x <$> p

_⊗_ : ∀ {NT Tok i₁ i₂ R₁ R₂} →
      Parser NT Tok i₁ R₁ → Parser NT Tok i₂ R₂ →
      Parser NT Tok _ (R₁ × R₂)
p₁ ⊗ p₂ = (_,_) <$> p₁ ⊛ p₂

_⊗!_ : ∀ {NT Tok i₁ c₂ R₁ R₂} →
       Parser NT Tok i₁ R₁ → Parser NT Tok (false ◇ c₂) R₂ →
       Parser NT Tok (false ◇ _) (R₁ × R₂)
p₁ ⊗! p₂ = (_,_) <$> p₁ ⊛! p₂

------------------------------------------------------------------------
-- Parsing sequences

infix 55 _⋆ _+

-- Not accepted by the productivity checker:

-- mutual

--   _⋆ : ∀ {NT Tok R c} →
--        Parser NT Tok (false ◇ c) R     →
--        Parser NT Tok _           (List R)
--   p ⋆ = return [] ∣ p +

--   _+ : ∀ {NT Tok R c} →
--        Parser NT Tok (false ◇ c) R     →
--        Parser NT Tok _           (List R)
--   p + = _∷_ <$> p ⊛ p ⋆

-- In fact the code above risks leading to infinite loops in the
-- current version of Agda (Mar 2009), since it does not contain any
-- coinductive constructors. The following code is OK, though:

mutual

  _⋆ : ∀ {NT Tok R c} →
       Parser NT Tok (false ◇ c) R        →
       Parser NT Tok _           (List R)
  p ⋆ = return [] ∣ p +

  _+ : ∀ {NT Tok R c} →
       Parser NT Tok (false ◇ c) R        →
       Parser NT Tok _           (List R)
  p + =  p   !>>= λ x  → ♯
        (p ⋆ ?>>= λ xs →
         return (x ∷ xs))

-- p sepBy⟨ ne ⟩ sep and p sepBy sep parse one or more ps separated by
-- seps.

_sepBy⟨_⟩_ : ∀ {NT Tok i i′ R R′} →
             Parser NT Tok i R →
             (empty i′ ∧ true) ∧ (empty i ∧ true) ≡ false →
             Parser NT Tok i′ R′ →
             Parser NT Tok _ (List R)
p sepBy⟨ non-empty ⟩ sep = _∷_ <$> p ⊛ cast₁ (sep ⊛> p) ⋆
  where cast₁ = cast non-empty refl

-- _sepBy_ could be implemented by using _sepBy⟨_⟩_, but the following
-- definition is handled more efficiently by the current version of
-- Agda (Dec 2008).

_sepBy_ : ∀ {NT Tok i c R R′} →
          Parser NT Tok i R → Parser NT Tok (false ◇ c) R′ →
          Parser NT Tok _ (List R)
p sepBy sep = _∷_ <$> p ⊛ (sep ⊛> p) ⋆

-- Note that the index of atLeast is only partly inferred; the
-- recursive structure of atLeast-index is given manually.

atLeast-index : Corners → ℕ → Index
atLeast-index c zero    = _
atLeast-index c (suc n) = _

-- At least n occurrences of p.

atLeast : ∀ {NT Tok c R} (n : ℕ) →
          Parser NT Tok (false ◇ c) R →
          Parser NT Tok (atLeast-index c n) (List R)
atLeast zero    p = p ⋆
atLeast (suc n) p = _∷_ <$> p ⊛ atLeast n p

-- exactly n p parses n occurrences of p.

exactly-index : Index → ℕ → Index
exactly-index i zero    = _
exactly-index i (suc n) = _

exactly : ∀ {NT Tok i R} n →
          Parser NT Tok i R →
          Parser NT Tok (exactly-index i n) (Vec R n)
exactly zero    p = return []
exactly (suc n) p = _∷_ <$> p ⊛ exactly n p

-- A function with a similar type:

sequence : ∀ {NT Tok i R n} →
           Vec (Parser NT Tok i R) n →
           Parser NT Tok (exactly-index i n) (Vec R n)
sequence []       = return []
sequence (p ∷ ps) = _∷_ <$> p ⊛ sequence ps

-- p between ps parses p repeatedly, between the elements of ps:
--   ∙ between (x ∷ y ∷ z ∷ []) ≈ x ∙ y ∙ z.

between-corners : Corners → ℕ → Corners
between-corners c′ zero    = _
between-corners c′ (suc n) = _

_between_ : ∀ {NT Tok i R c′ R′ n} →
            Parser NT Tok i R →
            Vec (Parser NT Tok (false ◇ c′) R′) (suc n) →
            Parser NT Tok (false ◇ between-corners c′ n) (Vec R n)
p between (x ∷ [])     = [] <$ x
p between (x ∷ y ∷ xs) = _∷_ <$> (x ⊛> p) ⊛ (p between (y ∷ xs))

------------------------------------------------------------------------
-- Chaining

-- Associativity. Used to specify how chain≥ should apply the parsed
-- operators: left or right associatively.

data Assoc : Set where
  left  : Assoc
  right : Assoc

-- Application.

appʳ : {R : Set} → R × (R → R → R) → R → R
appʳ (x , _•_) y = x • y

appˡ : ∀ {R} → R → (R → R → R) × R → R
appˡ x (_•_ , y) = x • y

-- Shifting. See Examples below for an illuminating example.

shiftʳ : ∀ {A B} → A → List (B × A) → List (A × B) × A
shiftʳ x  []                = ([] , x)
shiftʳ x₁ ((x₂ , x₃) ∷ xs₄) = ((x₁ , x₂) ∷ proj₁ xs₃x₄ , proj₂ xs₃x₄)
  where xs₃x₄ = shiftʳ x₃ xs₄

-- Post-processing for the chain≥ parser.

chain≥-combine : {R : Set} → Assoc → R → List ((R → R → R) × R) → R
chain≥-combine left  x ys = foldl appˡ x ys
chain≥-combine right x ys with shiftʳ x ys
... | (xs , y) = foldr appʳ y xs

-- Chains at least n occurrences of op, in an a-associative
-- manner. The ops are surrounded by ps.

chain≥ : ∀ {NT Tok c₁ i₂ R} (n : ℕ) →
         Assoc →
         Parser NT Tok (false ◇ c₁) R →
         Parser NT Tok i₂ (R → R → R) →
         Parser NT Tok _ R
chain≥ n a p op = chain≥-combine a <$> p ⊛ atLeast n (op ⊗! p)

private
 module Examples {R S : Set}
                 (x y z : R)
                 (a b : S)
                 (_+_ _*_ : R → R → R)
                 where

  ex : shiftʳ x ((a , y) ∷ (b , z) ∷ []) ≡ ((x , a) ∷ (y , b) ∷ [] , z)
  ex = refl

  exʳ : chain≥-combine right x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ x + (y * z)
  exʳ = refl

  exˡ : chain≥-combine left  x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ (x + y) * z
  exˡ = refl

------------------------------------------------------------------------
-- N-ary variants of _∣_

-- choice ps parses one of the elements in ps.

choice-corners : Corners → ℕ → Corners
choice-corners c zero    = _
choice-corners c (suc n) = _

choice : ∀ {NT Tok c R n} →
         Vec (Parser NT Tok (false ◇ c) R) n →
         Parser NT Tok (false ◇ choice-corners c n) R
choice []       = fail
choice (p ∷ ps) = p ∣ choice ps

-- choiceMap f xs ≈ choice (map f xs), but avoids use of Vec and
-- fromList.

choiceMap-corners : {A : Set} → (A → Corners) → List A → Corners
choiceMap-corners c []       = _
choiceMap-corners c (x ∷ xs) = _

choiceMap : ∀ {NT Tok R} {A : Set} {c : A → Corners} →
            ((x : A) → Parser NT Tok (false ◇ c x) R) →
            (xs : List A) →
            Parser NT Tok (false ◇ choiceMap-corners c xs) R
choiceMap f []       = fail
choiceMap f (x ∷ xs) = f x ∣ choiceMap f xs

------------------------------------------------------------------------
-- sat and friends

sat : ∀ {NT Tok R} → (Tok → Maybe R) → Parser NT Tok (0I · 1I) R
sat {NT} {Tok} {R} p = token !>>= λ c → ♯ ok (p c)
  where
  okIndex : Maybe R → Index
  okIndex nothing  = _
  okIndex (just _) = _

  ok : (x : Maybe R) → Parser NT Tok (okIndex x) R
  ok nothing  = fail
  ok (just x) = return x

sat' : ∀ {NT Tok} → (Tok → Bool) → Parser NT Tok _ ⊤
sat' p = sat (boolToMaybe ∘ p)

any : ∀ {NT Tok} → Parser NT Tok _ Tok
any = sat just

------------------------------------------------------------------------
-- Token parsers

module Token (A : DecSetoid zero zero) where

  open DecSetoid A using (_≟_) renaming (Carrier to Tok)

  -- Parses a given token (or, really, a given equivalence class of
  -- tokens).

  tok : ∀ {NT} → Tok → Parser NT Tok _ Tok
  tok tok = sat p
    where
    p : Tok → Maybe Tok
    p tok′ with tok ≟ tok′
    ... | yes _ = just tok′
    ... | no  _ = nothing

  -- Parses a sequence of tokens.

  theString : ∀ {NT n} → Vec Tok n → Parser NT Tok _ (Vec Tok n)
  theString cs = sequence (Vec.map tok cs)

------------------------------------------------------------------------
-- Character parsers

digit : ∀ {NT} → Parser NT Char _ ℕ
digit = 0 <$ tok '0'
      ∣ 1 <$ tok '1'
      ∣ 2 <$ tok '2'
      ∣ 3 <$ tok '3'
      ∣ 4 <$ tok '4'
      ∣ 5 <$ tok '5'
      ∣ 6 <$ tok '6'
      ∣ 7 <$ tok '7'
      ∣ 8 <$ tok '8'
      ∣ 9 <$ tok '9'
  where open Token Char.decSetoid

number : ∀ {NT} → Parser NT Char _ ℕ
number = toNum <$> digit +
  where
  toNum = foldr (λ n x → 10 * x + n) 0 ∘ reverse

-- whitespace recognises an incomplete but useful list of whitespace
-- characters.

whitespace : ∀ {NT} → Parser NT Char _ ⊤
whitespace = sat' isSpace
  where
  isSpace = λ c →
    (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')
