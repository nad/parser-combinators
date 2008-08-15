------------------------------------------------------------------------
-- Library parsers which do not require the complicated setup used in
-- RecursiveDescent.Inductive.Lib
------------------------------------------------------------------------

-- This module also provides more examples of parsers for which the
-- indices cannot be inferred.

module RecursiveDescent.Inductive.SimpleLib where

open import RecursiveDescent.Inductive
open import RecursiveDescent.Index

open import Data.Nat
open import Data.Vec hiding (_⊛_; _>>=_)
open import Data.Vec1 using (Vec₁; []; _∷_)
open import Data.List using ([_]; []; _∷_)
open import Relation.Nullary
open import Data.Product.Record hiding (_×_)
open import Data.Product using (_×_) renaming (_,_ to pair)
open import Data.Bool
open import Data.Function
open import Data.Maybe
open import Data.Unit
open import Data.Bool.Properties
open import Algebra
private
  module BCS = CommutativeSemiring Bool-commutativeSemiring-∨-∧
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

-- Note that the resulting index here cannot be inferred...

private

  exactly'-corners : Corners -> ℕ -> Corners
  exactly'-corners c zero    = _
  exactly'-corners c (suc n) = _

  exactly' : forall {tok nt c r} n ->
             Parser tok nt (false , c) r ->
             Parser tok nt (false , exactly'-corners c n)
                           (Vec r (suc n))
  exactly' zero    p = singleton <$> p
  exactly' (suc n) p = _∷_ <$> p ⊛ exactly' n p

-- ...so we might as well generalise the function a little.
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

choiceMap-corners : forall {a} -> (a -> Corners) -> [ a ] -> Corners
choiceMap-corners c []       = _
choiceMap-corners c (x ∷ xs) = _

choiceMap : forall {tok nt r a} {c : a -> Corners} ->
            ((x : a) -> Parser tok nt (false , c x) r) ->
            (xs : [ a ]) ->
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
