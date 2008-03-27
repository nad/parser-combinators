------------------------------------------------------------------------
-- Terminating parser combinator interface
------------------------------------------------------------------------

module RecursiveDescent.Coinductive.Plain where

open import RecursiveDescent.Type public
import RecursiveDescent.Coinductive.Plain.Internal as P

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec
open import Logic
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Exported parser type

private

  data Parser' (tok : Set) (r : Set) : Set1 where
    mkP : forall {i} -> P.Parser tok i r -> Parser' tok r

Parser : Set -> Set -> Set1
Parser = Parser'

index : forall {tok r} -> Parser tok r -> Index
index (mkP {i} p) = i

empty : forall {tok r} -> Parser tok r -> Empty
empty p = proj₁ (index p)

private

  parser : forall {tok r} ->
           (p : Parser tok r) -> P.Parser tok (index p) r
  parser (mkP p) = p

------------------------------------------------------------------------
-- Run function for the parsers

parse : forall {tok r} ->
        Parser tok r -> [ tok ] -> [ Prod._×_ r [ tok ] ]
parse p s = map (Prod.map-× id BVec.toList)
                (P.parse _ (parser p) (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {tok r} -> Parser tok r -> [ tok ] -> [ r ]
parse-complete p s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p s))

------------------------------------------------------------------------
-- Exported combinators

infixl 50 _⊛_
infixl 40 _∣_
infixl 10 _!>>=_

symbol : forall {tok} -> Parser tok tok
symbol = mkP P.symbol

return : forall {tok r} -> r -> Parser tok r
return x = mkP (P.ret x)

fail : forall {tok r} -> Parser tok r
fail = mkP P.fail

-- The following function looks horrible because Agda lacks support
-- for pattern matching on record values.

_⊛_ : forall {tok r₁ r₂} ->
      Parser tok (r₁ -> r₂) -> Parser tok r₁ -> Parser tok r₂
mkP {i} p₁ ⊛ p₂ with inspect (proj₁ i)
... | true  with-≡ eq = mkP (P.seq₀ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
... | false with-≡ eq = mkP (P.seq₁ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl

-- Note that the first argument to bind must not accept the empty
-- string. (This is the reason for using a non-standard name for
-- bind.)

NonEmpty : forall {tok r} -> Parser tok r -> Set
NonEmpty p = True (empty p Bool-≟ false)

_!>>=_ : forall {tok r₁ r₂} ->
         (p : Parser tok r₁) -> {ne : NonEmpty p} ->
         (r₁ -> Parser tok r₂) ->
         Parser tok r₂
_!>>=_ (mkP p₁) {ne} p₂ =
  mkP (P.bind₁ (P.cast lem p₁) (\x -> parser (p₂ x)))
  where lem = ≡-cong₂ (_,_) (witnessToTruth ne) ≡-refl

_∣_ : forall {tok r} ->
      Parser tok r -> Parser tok r -> Parser tok r
mkP {i} p₁ ∣ p₂ with inspect (proj₁ i)
... | true  with-≡ eq = mkP (P.alt₀   (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
... | false with-≡ eq = mkP (P.alt₁ _ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
