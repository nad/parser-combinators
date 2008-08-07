------------------------------------------------------------------------
-- Some defined parsers
------------------------------------------------------------------------

-- Note that the fixpoint combinator ensures that _⋆ can be defined
-- without any need for library grammars (c.f.
-- RecursiveDescent.Inductive.Lib). However, use of the fixpoint
-- combinator can lead to code which is hard to understand, and should
-- be kept at a minimum.

-- This module also provides an example of a parser for which the
-- Index cannot be inferred.

module RecursiveDescent.InductiveWithFix.Lib where

open import RecursiveDescent.Index
open import RecursiveDescent.InductiveWithFix
open import Utilities

open import Data.Nat hiding (_≟_)
import Data.Vec  as V;  open V  using (Vec)
import Data.Vec1 as V₁; open V₁ using (Vec₁)
import Data.List as L ; open L  using ([_])
open import Relation.Nullary
open import Data.Product.Record
open import Data.Product renaming (_,_ to pair)
open import Data.Bool
open import Data.Function
open import Data.Maybe
open import Data.Unit

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 50 _⊛_ _<⊛_ _⊛>_ _<$>_ _<$_

_⊛_ : forall {tok nt i₁ i₂ r₁ r₂} ->
      Parser tok nt i₁ (r₁ -> r₂) ->
      Parser tok nt i₂ r₁ ->
      Parser tok nt _  r₂
p₁ ⊛ p₂ = p₁ >>= \f -> p₂ >>= \x -> return (f x)

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

------------------------------------------------------------------------
-- Parsing sequences

infix 55 _⋆ _+

_⋆ : forall {tok nt c r} ->
     Parser tok nt (false , c) r ->
     Parser tok nt _ [ r ]
p ⋆ = fix (return L.[] ∣ L._∷_ <$> lift p ⊛ ! fresh)

_+ : forall {tok nt c r} ->
     Parser tok nt (false , c) r ->
     Parser tok nt _ [ r ]
p + = L._∷_ <$> p ⊛ p ⋆

chain₁ :  forall {tok nt c₁ i₂ r}
       -> Assoc
       -> Parser tok nt (false , c₁) r
       -> Parser tok nt i₂ (r -> r -> r)
       -> Parser tok nt _ r
chain₁ a p op = chain₁-combine a <$> (pair <$> p ⊛ op) ⋆ ⊛ p

chain :  forall {tok nt c₁ i₂ r}
      -> Assoc
      -> Parser tok nt (false , c₁) r
      -> Parser tok nt i₂ (r -> r -> r)
      -> r
      -> Parser tok nt _ r
chain a p op x = return x ∣ chain₁ a p op

-- Note that the resulting index here cannot be inferred...

private

  exactly'-corners : Corners -> ℕ -> Corners
  exactly'-corners c zero    = _
  exactly'-corners c (suc n) = _

  exactly' : forall {tok nt c r} n ->
             Parser tok nt (false , c) r ->
             Parser tok nt (false , exactly'-corners c n)
                           (Vec r (suc n))
  exactly' zero    p = V.singleton <$> p
  exactly' (suc n) p = V._∷_ <$> p ⊛ exactly' n p

-- ...so we might as well generalise the function a little.
-- exactly n p parses n occurrences of p.

exactly-index : Index -> ℕ -> Index
exactly-index i zero    = _
exactly-index i (suc n) = _

exactly : forall {tok nt i r} n ->
          Parser tok nt i r ->
          Parser tok nt (exactly-index i n) (Vec r n)
exactly zero    p = return V.[]
exactly (suc n) p = V._∷_ <$> p ⊛ exactly n p

-- A function with a similar type:

sequence : forall {tok nt i r n} ->
           Vec₁ (Parser tok nt i r) n ->
           Parser tok nt (exactly-index i n) (Vec r n)
sequence V₁.[]         = return V.[]
sequence (V₁._∷_ p ps) = V._∷_ <$> p ⊛ sequence ps

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
-- Some parsers which require a decidable token equality

open import Relation.Binary

module Token (D : DecSetoid) where

  open DecSetoid D using (_≟_) renaming (carrier to tok)
  open import Data.Vec1

  -- Parsing a given token (or, really, a given equivalence class of
  -- tokens).

  sym : forall {nt} -> tok -> Parser tok nt _ tok
  sym c = sat p
    where
    p : tok -> Maybe tok
    p x with c ≟ x
    ... | yes _ = just x
    ... | no  _ = nothing

  -- Parsing a sequence of tokens.

  string : forall {nt n} -> Vec tok n -> Parser tok nt _ (Vec tok n)
  string cs = sequence (map₀₁ sym cs)

------------------------------------------------------------------------
-- Character parsers

import Data.Char as C
open C using (Char; _==_)
open Token C.decSetoid

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

number : forall {nt} -> Parser Char nt _ ℕ
number = toNum <$> digit +
  where toNum = L.foldr (\n x -> 10 * x + n) 0 ∘ L.reverse

-- whitespace recognises an incomplete but useful list of whitespace
-- characters.

whitespace : forall {nt} -> Parser Char nt _ ⊤
whitespace = sat' isSpace
  where
  isSpace = \c -> (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')
