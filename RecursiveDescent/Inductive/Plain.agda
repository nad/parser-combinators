------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Plain where

open import RecursiveDescent.Type public
import RecursiveDescent.Inductive.Plain.Internal as P

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec
open import Relation.Nullary
open import Logic
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Exported parser type

private

  data Parser' (tok : Set) (nt : ParserType) (r : Set) : Set1 where
    mkP : forall {i} -> P.Parser tok nt i r -> Parser' tok nt r

Parser : Set -> ParserType -> Set -> Set1
Parser = Parser'

index : forall {tok nt r} -> Parser tok nt r -> Index
index (mkP {i} p) = i

empty : forall {tok nt r} -> Parser tok nt r -> Empty
empty p = proj₁ (index p)

private

  parser : forall {tok nt r} ->
           (p : Parser tok nt r) -> P.Parser tok nt (index p) r
  parser (mkP p) = p

infix 0 ∷=_

data RestrictedParser (tok : Set) (nt : ParserType)
                      (r : Set) (i : Index) : Set1 where
  ∷=_ : (p : Parser tok nt r) {ok : True (index p Index-≟ i)} ->
        RestrictedParser tok nt r i

LibraryGrammar : (ParserType -> ParserType) -> Set -> ParserType -> Set1
LibraryGrammar NT tok nt = forall {i r} ->
  NT nt i r -> RestrictedParser tok nt r i

Grammar : Set -> ParserType -> Set1
Grammar = LibraryGrammar (\nt -> nt)

------------------------------------------------------------------------
-- Run function for the parsers

parse :  forall {tok nt r}
      -> Parser tok nt r -> Grammar tok nt
      -> [ tok ] -> [ Prod._×_ r [ tok ] ]
parse {tok} {nt} p g s = map (Prod.map-× id BVec.toList)
                             (P.parse g' _ (parser p) (BVec.fromList s))
  where
  g' : P.Grammar tok nt
  g' {r = r} x with g x
  ... | ∷=_ (mkP p') {ne} = P.cast (witnessToTruth ne) p'

-- A variant which only returns parses which leave no remaining input.

parse-complete :  forall {tok nt r}
               -> Parser tok nt r -> Grammar tok nt
               -> [ tok ] -> [ r ]
parse-complete p g s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p g s))

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 50 _⊛_
infixl 40 _∣_
infixl 10 _!>>=_

!_ : forall {tok nt i r} ->
     nt i r -> Parser tok nt r
! x = mkP (P.!_ x)

symbol : forall {tok nt} -> Parser tok nt tok
symbol = mkP P.symbol

return : forall {tok nt r} -> r -> Parser tok nt r
return x = mkP (P.ret x)

fail : forall {tok nt r} -> Parser tok nt r
fail = mkP P.fail

-- The following function looks horrible because Agda lacks support
-- for pattern matching on record values.

_⊛_ : forall {tok nt r₁ r₂} ->
      Parser tok nt (r₁ -> r₂) -> Parser tok nt r₁ -> Parser tok nt r₂
mkP {i} p₁ ⊛ p₂ with inspect (proj₁ i)
... | true  with-≡ eq = mkP (P.seq₀ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
... | false with-≡ eq = mkP (P.seq₁ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl

-- Note that the first argument to bind must not accept the empty
-- string. (This is the reason for using a non-standard name for
-- bind.)

NonEmpty : forall {tok nt r} -> Parser tok nt r -> Set
NonEmpty p = True (empty p Bool-≟ false)

_!>>=_ : forall {tok nt r₁ r₂} ->
         (p : Parser tok nt r₁) -> {ne : NonEmpty p} ->
         (r₁ -> Parser tok nt r₂) ->
         Parser tok nt r₂
_!>>=_ (mkP p₁) {ne} p₂ =
  mkP (P.bind (P.cast lem p₁) (\x -> parser (p₂ x)))
  where lem = ≡-cong₂ (_,_) (witnessToTruth ne) ≡-refl

_∣_ : forall {tok nt r} ->
      Parser tok nt r -> Parser tok nt r -> Parser tok nt r
mkP {i} p₁ ∣ p₂ with inspect (proj₁ i)
... | true  with-≡ eq = mkP (P.alt₀   (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
... | false with-≡ eq = mkP (P.alt₁ _ (P.cast lem p₁) (parser p₂))
  where lem = ≡-cong₂ (_,_) (≡-sym eq) ≡-refl
