------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

-- This module also provides examples of parsers for which the indices
-- cannot be inferred.

module StructurallyRecursiveDescentParsing.Lib where

open import StructurallyRecursiveDescentParsing.Interface
import StructurallyRecursiveDescentParsing.Type as Type
open import StructurallyRecursiveDescentParsing.Index

open import Data.Nat hiding (_≟_)
open import Data.Vec  using (Vec;  []; _∷_)
open import Data.Vec1 using (Vec₁; []; _∷_; map₀₁)
open import Data.List using (List; []; _∷_; foldr; foldl; reverse)
open import Data.Product
open import Data.Bool
open import Data.Function
open import Data.Maybe
open import Data.Unit
import Data.Char as Char
open Char using (Char; _==_)
open import Algebra
open import Data.Bool.Properties
private
  module BCS = CommutativeSemiring Bool-commutativeSemiring-∨-∧
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _⊛!_ _<⊛_ _⊛>_ _<$>_ _<$_ _⊗_ _⊗!_

_⊛_ : forall {Tok NT i₁ i₂ R₁ R₂} ->
      Parser Tok NT i₁ (R₁ -> R₂) ->
      Parser Tok NT i₂ R₁ ->
      Parser Tok NT _  R₂
p₁ ⊛ p₂ = p₁ >>= \f -> p₂ >>= \x -> return (f x)

-- A variant: If the second parser does not accept the empty string,
-- then neither does the combination. (This is immediate for the first
-- parser, but for the second one a small lemma is needed, hence this
-- variant.)

_⊛!_ : forall {Tok NT i₁ c₂ R₁ R₂} ->
       Parser Tok NT i₁ (R₁ -> R₂) ->
       Parser Tok NT (false ◇ c₂) R₁ ->
       Parser Tok NT (false ◇ _)  R₂
_⊛!_ {i₁ = i₁} p₁ p₂ = cast (BCS.*-comm (empty i₁) false) ≡-refl
                            (p₁ ⊛ p₂)

_<$>_ : forall {Tok NT i R₁ R₂} ->
        (R₁ -> R₂) ->
        Parser Tok NT i R₁ ->
        Parser Tok NT _ R₂
f <$> x = return f ⊛ x

_<⊛_ : forall {Tok NT i₁ i₂ R₁ R₂} ->
       Parser Tok NT i₁ R₁ ->
       Parser Tok NT i₂ R₂ ->
       Parser Tok NT _ R₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {Tok NT i₁ i₂ R₁ R₂} ->
       Parser Tok NT i₁ R₁ ->
       Parser Tok NT i₂ R₂ ->
       Parser Tok NT _ R₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {Tok NT i R₁ R₂} ->
       R₁ ->
       Parser Tok NT i R₂ ->
       Parser Tok NT _ R₁
x <$ y = const x <$> y

_⊗_ : forall {Tok NT i₁ i₂ R₁ R₂} ->
      Parser Tok NT i₁ R₁ -> Parser Tok NT i₂ R₂ ->
      Parser Tok NT _ (R₁ × R₂)
p₁ ⊗ p₂ = (_,_) <$> p₁ ⊛ p₂

_⊗!_ : forall {Tok NT i₁ c₂ R₁ R₂} ->
      Parser Tok NT i₁ R₁ -> Parser Tok NT (false ◇ c₂) R₂ ->
      Parser Tok NT (false ◇ _) (R₁ × R₂)
p₁ ⊗! p₂ = (_,_) <$> p₁ ⊛! p₂

------------------------------------------------------------------------
-- Parsing sequences

infix 55 _⋆ _+

-- Not accepted by the productivity checker:

-- mutual

--   _⋆ : forall {Tok R d} ->
--        Parser Tok (false ◇ d) R     ->
--        Parser Tok _           (List R)
--   p ⋆ ~ return [] ∣ p +

--   _+ : forall {Tok R d} ->
--        Parser Tok (false ◇ d) R     ->
--        Parser Tok _           (List R)
--   p + ~ _∷_ <$> p ⊛ p ⋆

-- By inlining some definitions we can show that the definitions are
-- productive, though. The following definitions have also been
-- simplified:

mutual

  _⋆ : forall {Tok NT R d} ->
       Parser Tok NT (false ◇ d) R     ->
       Parser Tok NT _           (List R)
  p ⋆ ~ Type.alt _ _ (return []) (p +)

  _+ : forall {Tok NT R d} ->
       Parser Tok NT (false ◇ d) R     ->
       Parser Tok NT _           (List R)
  p + ~ Type._!>>=_ p     \x  ->
        Type._?>>=_ (p ⋆) \xs ->
        return (x ∷ xs)

-- p sepBy sep parses one or more ps separated by seps.

_sepBy_ : forall {Tok NT R R′ i d} ->
          Parser Tok NT i R -> Parser Tok NT (false ◇ d) R′ ->
          Parser Tok NT _ (List R)
p sepBy sep = _∷_ <$> p ⊛ (sep ⊛> p) ⋆

-- Note that the index of atLeast is only partly inferred; the
-- recursive structure of atLeast-index is given manually.

atLeast-index : Corners -> ℕ -> Index
atLeast-index c zero    = _
atLeast-index c (suc n) = _

-- At least n occurrences of p.

atLeast : forall {Tok NT c R} (n : ℕ) ->
          Parser Tok NT (false ◇ c) R ->
          Parser Tok NT (atLeast-index c n) (List R)
atLeast zero    p = p ⋆
atLeast (suc n) p = _∷_ <$> p ⊛ atLeast n p

-- exactly n p parses n occurrences of p.

exactly-index : Index -> ℕ -> Index
exactly-index i zero    = _
exactly-index i (suc n) = _

exactly : forall {Tok NT i R} n ->
          Parser Tok NT i R ->
          Parser Tok NT (exactly-index i n) (Vec R n)
exactly zero    p = return []
exactly (suc n) p = _∷_ <$> p ⊛ exactly n p

-- A function with a similar type:

sequence : forall {Tok NT i R n} ->
           Vec₁ (Parser Tok NT i R) n ->
           Parser Tok NT (exactly-index i n) (Vec R n)
sequence []       = return []
sequence (p ∷ ps) = _∷_ <$> p ⊛ sequence ps

-- p between ps parses p repeatedly, between the elements of ps:
--   ∙ between (x ∷ y ∷ z ∷ []) ≈ x ∙ y ∙ z.

between-corners : Corners -> ℕ -> Corners
between-corners c′ zero    = _
between-corners c′ (suc n) = _

_between_ : forall {Tok NT i R c′ R′ n} ->
            Parser Tok NT i R ->
            Vec₁ (Parser Tok NT (false ◇ c′) R′) (suc n) ->
            Parser Tok NT (false ◇ between-corners c′ n) (Vec R n)
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

appʳ : forall {R} -> R × (R -> R -> R) -> R -> R
appʳ (x , _•_) y = x • y

appˡ : forall {R} -> R -> (R -> R -> R) × R -> R
appˡ x (_•_ , y) = x • y

-- Shifting. See Examples below for an illuminating example.

shiftʳ : forall {A B} -> A -> List (B × A) -> List (A × B) × A
shiftʳ x  []                = ([] , x)
shiftʳ x₁ ((x₂ , x₃) ∷ xs₄) = ((x₁ , x₂) ∷ proj₁ xs₃x₄ , proj₂ xs₃x₄)
  where xs₃x₄ = shiftʳ x₃ xs₄

-- Post-processing for the chain≥ parser.

chain≥-combine : forall {R} ->
                 Assoc -> R -> List ((R -> R -> R) × R) -> R
chain≥-combine right x ys = uncurry (flip (foldr appʳ)) (shiftʳ x ys)
chain≥-combine left  x ys = foldl appˡ x ys

-- Chains at least n occurrences of op, in an a-associative
-- manner. The ops are surrounded by ps.

chain≥ : forall {Tok NT c₁ i₂ R} (n : ℕ) ->
         Assoc ->
         Parser Tok NT (false ◇ c₁) R ->
         Parser Tok NT i₂ (R -> R -> R) ->
         Parser Tok NT _ R
chain≥ n a p op = chain≥-combine a <$> p ⊛ atLeast n (op ⊗! p)

private
 module Examples {R S : Set}
                 (x y z : R)
                 (a b : S)
                 (_+_ _*_ : R -> R -> R)
                 where

  ex : shiftʳ x ((a , y) ∷ (b , z) ∷ []) ≡ ((x , a) ∷ (y , b) ∷ [] , z)
  ex = ≡-refl

  exʳ : chain≥-combine right x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ x + (y * z)
  exʳ = ≡-refl

  exˡ : chain≥-combine left  x ((_+_ , y) ∷ (_*_ , z) ∷ []) ≡ (x + y) * z
  exˡ = ≡-refl

------------------------------------------------------------------------
-- N-ary variants of _∣_

-- choice ps parses one of the elements in ps.

choice-corners : Corners -> ℕ -> Corners
choice-corners c zero    = _
choice-corners c (suc n) = _

choice : forall {Tok NT c R n} ->
         Vec₁ (Parser Tok NT (false ◇ c) R) n ->
         Parser Tok NT (false ◇ choice-corners c n) R
choice []       = fail
choice (p ∷ ps) = p ∣ choice ps

-- choiceMap f xs ≈ choice (map f xs), but avoids use of Vec₁ and
-- fromList.

choiceMap-corners : forall {A} -> (A -> Corners) -> List A -> Corners
choiceMap-corners c []       = _
choiceMap-corners c (x ∷ xs) = _

choiceMap : forall {Tok NT R A} {c : A -> Corners} ->
            ((x : A) -> Parser Tok NT (false ◇ c x) R) ->
            (xs : List A) ->
            Parser Tok NT (false ◇ choiceMap-corners c xs) R
choiceMap f []       = fail
choiceMap f (x ∷ xs) = f x ∣ choiceMap f xs

------------------------------------------------------------------------
-- sat and friends

sat : forall {Tok NT R} ->
      (Tok -> Maybe R) -> Parser Tok NT (0I ·I 1I) R
sat {Tok} {NT} {R} p = token !>>= \c -> ok (p c)
  where
  okIndex : Maybe R -> Index
  okIndex nothing  = _
  okIndex (just _) = _

  ok : (x : Maybe R) -> Parser Tok NT (okIndex x) R
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {Tok NT} -> (Tok -> Bool) -> Parser Tok NT _ ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {Tok NT} -> Parser Tok NT _ Tok
any = sat just

------------------------------------------------------------------------
-- Token parsers

module Token (A : DecSetoid) where

  open DecSetoid A using (_≟_) renaming (carrier to Tok)

  -- Parses a given token (or, really, a given equivalence class of
  -- tokens).

  theToken : forall {NT} -> Tok -> Parser Tok NT _ Tok
  theToken tok = sat p
    where
    p : Tok -> Maybe Tok
    p tok′ with tok ≟ tok′
    ... | yes _ = just tok′
    ... | no  _ = nothing

  -- Parses a sequence of tokens.

  theString : forall {NT n} -> Vec Tok n -> Parser Tok NT _ (Vec Tok n)
  theString cs = sequence (map₀₁ theToken cs)

------------------------------------------------------------------------
-- Character parsers

digit : forall {NT} -> Parser Char NT _ ℕ
digit = 0 <$ theToken '0'
      ∣ 1 <$ theToken '1'
      ∣ 2 <$ theToken '2'
      ∣ 3 <$ theToken '3'
      ∣ 4 <$ theToken '4'
      ∣ 5 <$ theToken '5'
      ∣ 6 <$ theToken '6'
      ∣ 7 <$ theToken '7'
      ∣ 8 <$ theToken '8'
      ∣ 9 <$ theToken '9'
  where open Token Char.decSetoid

number : forall {NT} -> Parser Char NT _ ℕ
number = toNum <$> digit +
  where
  toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse

-- whitespace recognises an incomplete but useful list of whitespace
-- characters.

whitespace : forall {NT} -> Parser Char NT _ ⊤
whitespace = sat' isSpace
  where
  isSpace = \c ->
    (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')
