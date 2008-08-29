------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

-- This module also provides examples of parsers for which the indices
-- cannot be inferred.

module RecursiveDescent.Hybrid.Lib where

open import RecursiveDescent.Hybrid
import RecursiveDescent.Hybrid.Internal as Internal
open import RecursiveDescent.Index
open import Utilities

open import Data.Nat hiding (_≟_)
open import Data.Vec  using (Vec;  []; _∷_)
open import Data.Vec1 using (Vec₁; []; _∷_; map₀₁)
open import Data.List using (List; []; _∷_; foldr; reverse)
open import Data.Product.Record hiding (_×_)
open import Data.Product using (_×_) renaming (_,_ to pair)
open import Data.Bool
open import Data.Function
open import Data.Maybe
open import Data.Unit
open import Data.Bool.Properties
import Data.Char as Char
open Char using (Char; _==_)
open import Algebra
private
  module BCS = CommutativeSemiring Bool-commutativeSemiring-∨-∧
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _⊛!_ _<⊛_ _⊛>_ _<$>_ _<$_ _⊗_ _⊗!_

_⊛_ : forall {tok nt i₁ i₂ r₁ r₂} ->
      Parser tok nt i₁ (r₁ -> r₂) ->
      Parser tok nt i₂ r₁ ->
      Parser tok nt _  r₂
p₁ ⊛ p₂ = p₁ >>= \f -> p₂ >>= \x -> return (f x)

-- A variant: If the second parser does not accept the empty string,
-- then neither does the combination. (This is immediate for the first
-- parser, but for the second one a small lemma is needed, hence this
-- variant.)

_⊛!_ : forall {tok nt i₁ c₂ r₁ r₂} ->
       Parser tok nt i₁ (r₁ -> r₂) ->
       Parser tok nt (false , c₂) r₁ ->
       Parser tok nt (false , _)  r₂
_⊛!_ {i₁ = i₁} p₁ p₂ = cast (BCS.*-comm (proj₁ i₁) false) ≡-refl
                            (p₁ ⊛ p₂)

_<$>_ : forall {tok nt i r₁ r₂} ->
        (r₁ -> r₂) ->
        Parser tok nt i r₁ ->
        Parser tok nt _ r₂
f <$> x = return f ⊛ x

_<⊛_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok nt i₁ i₂ r₁ r₂} ->
       Parser tok nt i₁ r₁ ->
       Parser tok nt i₂ r₂ ->
       Parser tok nt _ r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok nt i r₁ r₂} ->
       r₁ ->
       Parser tok nt i r₂ ->
       Parser tok nt _ r₁
x <$ y = const x <$> y

_⊗_ : forall {tok nt i₁ i₂ r₁ r₂} ->
      Parser tok nt i₁ r₁ -> Parser tok nt i₂ r₂ ->
      Parser tok nt _ (r₁ × r₂)
p₁ ⊗ p₂ = pair <$> p₁ ⊛ p₂

_⊗!_ : forall {tok nt i₁ c₂ r₁ r₂} ->
      Parser tok nt i₁ r₁ -> Parser tok nt (false , c₂) r₂ ->
      Parser tok nt (false , _) (r₁ × r₂)
p₁ ⊗! p₂ = pair <$> p₁ ⊛! p₂

------------------------------------------------------------------------
-- Parsing sequences

infix 55 _⋆ _+

-- Not accepted by the productivity checker:

-- mutual

--   _⋆ : forall {tok r d} ->
--        Parser tok (false , d) r     ->
--        Parser tok _           (List r)
--   p ⋆ ~ return [] ∣ p +

--   _+ : forall {tok r d} ->
--        Parser tok (false , d) r     ->
--        Parser tok _           (List r)
--   p + ~ _∷_ <$> p ⊛ p ⋆

-- By inlining some definitions we can show that the definitions are
-- productive, though. The following definitions have also been
-- simplified:

mutual

  _⋆ : forall {tok nt r d} ->
       Parser tok nt (false , d) r     ->
       Parser tok nt _           (List r)
  p ⋆ ~ Internal.alt _ _ (return []) (p +)

  _+ : forall {tok nt r d} ->
       Parser tok nt (false , d) r     ->
       Parser tok nt _           (List r)
  p + ~ Internal.bind₂ p     \x  ->
        Internal.bind₁ (p ⋆) \xs ->
        return (x ∷ xs)

-- p sepBy sep parses one or more ps separated by seps.

_sepBy_ : forall {tok nt r r' i d} ->
          Parser tok nt i r -> Parser tok nt (false , d) r' ->
          Parser tok nt _ (List r)
p sepBy sep = _∷_ <$> p ⊛ (sep ⊛> p) ⋆

-- Note that the index of atLeast is only partly inferred; the
-- recursive structure of atLeast-index is given manually.

atLeast-index : Corners -> ℕ -> Index
atLeast-index c zero    = _
atLeast-index c (suc n) = _

-- At least n occurrences of p.

atLeast : forall {tok nt c r} (n : ℕ) ->
          Parser tok nt (false , c) r ->
          Parser tok nt (atLeast-index c n) (List r)
atLeast zero    p = p ⋆
atLeast (suc n) p = _∷_ <$> p ⊛ atLeast n p

-- Chains at least n occurrences of op, in an a-associative
-- manner. The ops are surrounded by ps.

chain≥ : forall {tok nt c₁ i₂ r} (n : ℕ) ->
         Assoc ->
         Parser tok nt (false , c₁) r ->
         Parser tok nt i₂ (r -> r -> r) ->
         Parser tok nt _ r
chain≥ n a p op = chain≥-combine a <$> p ⊛ atLeast n (op ⊗! p)

-- exactly n p parses n occurrences of p.

exactly-index : Index -> ℕ -> Index
exactly-index i zero    = _
exactly-index i (suc n) = _

exactly : forall {tok nt i r} n ->
          Parser tok nt i r ->
          Parser tok nt (exactly-index i n) (Vec r n)
exactly zero    p = return []
exactly (suc n) p = _∷_ <$> p ⊛ exactly n p

-- A function with a similar type:

sequence : forall {tok nt i r n} ->
           Vec₁ (Parser tok nt i r) n ->
           Parser tok nt (exactly-index i n) (Vec r n)
sequence []       = return []
sequence (p ∷ ps) = _∷_ <$> p ⊛ sequence ps

-- p between ps parses p repeatedly, between the elements of ps:
--   ∙ between (x ∷ y ∷ z ∷ []) ≈ x ∙ y ∙ z.

between-corners : Corners -> ℕ -> Corners
between-corners c′ zero    = _
between-corners c′ (suc n) = _

_between_ : forall {tok nt i r c′ r′ n} ->
            Parser tok nt i r ->
            Vec₁ (Parser tok nt (false , c′) r′) (suc n) ->
            Parser tok nt (false , between-corners c′ n) (Vec r n)
p between (x ∷ [])     = [] <$ x
p between (x ∷ y ∷ xs) = _∷_ <$> (x ⊛> p) ⊛ (p between (y ∷ xs))

------------------------------------------------------------------------
-- N-ary variants of _∣_

-- choice ps parses one of the elements in ps.

choice-corners : Corners -> ℕ -> Corners
choice-corners c zero    = _
choice-corners c (suc n) = _

choice : forall {tok nt c r n} ->
         Vec₁ (Parser tok nt (false , c) r) n ->
         Parser tok nt (false , choice-corners c n) r
choice []       = fail
choice (p ∷ ps) = p ∣ choice ps

-- choiceMap f xs ≈ choice (map f xs), but avoids use of Vec₁ and
-- fromList.

choiceMap-corners : forall {a} -> (a -> Corners) -> List a -> Corners
choiceMap-corners c []       = _
choiceMap-corners c (x ∷ xs) = _

choiceMap : forall {tok nt r a} {c : a -> Corners} ->
            ((x : a) -> Parser tok nt (false , c x) r) ->
            (xs : List a) ->
            Parser tok nt (false , choiceMap-corners c xs) r
choiceMap f []       = fail
choiceMap f (x ∷ xs) = f x ∣ choiceMap f xs

------------------------------------------------------------------------
-- sat and friends

sat : forall {tok nt r} ->
      (tok -> Maybe r) -> Parser tok nt (0I ·I 1I) r
sat {tok} {nt} {r} p = symbol !>>= \c -> ok (p c)
  where
  okIndex : Maybe r -> Index
  okIndex nothing  = _
  okIndex (just _) = _

  ok : (x : Maybe r) -> Parser tok nt (okIndex x) r
  ok nothing  = fail
  ok (just x) = return x

sat' : forall {tok nt} -> (tok -> Bool) -> Parser tok nt _ ⊤
sat' p = sat (boolToMaybe ∘ p)

any : forall {tok nt} -> Parser tok nt _ tok
any = sat just

------------------------------------------------------------------------
-- Token parsers

module Token (a : DecSetoid) where

  open DecSetoid a using (_≟_) renaming (carrier to tok)

  -- Parses a given token (or, really, a given equivalence class of
  -- tokens).

  sym : forall {nt} -> tok -> Parser tok nt _ tok
  sym x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing

  -- Parses a sequence of tokens.

  string : forall {nt n} -> Vec tok n -> Parser tok nt _ (Vec tok n)
  string cs = sequence (map₀₁ sym cs)

------------------------------------------------------------------------
-- Character parsers

digit : forall {nt} -> Parser Char nt _ ℕ
digit = 0 <$ sym '0'
      ∣ 1 <$ sym '1'
      ∣ 2 <$ sym '2'
      ∣ 3 <$ sym '3'
      ∣ 4 <$ sym '4'
      ∣ 5 <$ sym '5'
      ∣ 6 <$ sym '6'
      ∣ 7 <$ sym '7'
      ∣ 8 <$ sym '8'
      ∣ 9 <$ sym '9'
  where open Token Char.decSetoid

number : forall {nt} -> Parser Char nt _ ℕ
number = toNum <$> digit +
  where
  toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse

-- whitespace recognises an incomplete but useful list of whitespace
-- characters.

whitespace : forall {nt} -> Parser Char nt _ ⊤
whitespace = sat' isSpace
  where
  isSpace = \c ->
    (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')
