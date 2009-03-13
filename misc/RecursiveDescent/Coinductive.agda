------------------------------------------------------------------------
-- Terminating parser combinator interface
------------------------------------------------------------------------

module RecursiveDescent.Coinductive where

open import RecursiveDescent.Index
import RecursiveDescent.Coinductive.Internal as P
open P public using (Parser)

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record hiding (map)
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec

------------------------------------------------------------------------
-- Run function for the parsers

parse : forall {tok i r} ->
        Parser tok i r -> List tok -> List (Prod._×_ r (List tok))
parse p s = map (Prod.map id BVec.toList)
                (P.parse _ p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {tok i r} ->
                 Parser tok i r -> List tok -> List r
parse-complete p s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p s))

------------------------------------------------------------------------
-- Exported combinators

infixl 40 _∣_
infixl 10 _>>=_ _!>>=_

symbol : forall {tok} -> Parser tok 0I tok
symbol = P.symbol

return : forall {tok r} -> r -> Parser tok 1I r
return = P.ret

fail : forall {tok r} -> Parser tok 0I r
fail = P.fail

_>>=_ : forall {tok e₁ c₁ i₂ r₁ r₂} -> let i₁ = (e₁ , c₁) in
        Parser tok i₁ r₁ ->
        (r₁ -> Parser tok i₂ r₂) ->
        Parser tok (i₁ ·I i₂) r₂
_>>=_ {e₁ = true } = P.bind₀
_>>=_ {e₁ = false} = P.bind₁

-- If the first parser is guaranteed to consume something, then the
-- second parser's index can depend on the result of the first parser.

_!>>=_ : forall {tok c₁ r₁ r₂} {i₂ : r₁ -> Index} ->
         let i₁ = (false , c₁) in
         Parser tok i₁ r₁ ->
         ((x : r₁) -> Parser tok (i₂ x) r₂) ->
         Parser tok (i₁ ·I 1I) r₂
_!>>=_ = P.bind₁

_∣_ : forall {tok e₁ c₁ i₂ r} -> let i₁ = (e₁ , c₁) in
      Parser tok i₁ r ->
      Parser tok i₂ r ->
      Parser tok (i₁ ∣I i₂) r
_∣_ {e₁ = true } = P.alt₀
_∣_ {e₁ = false} = P.alt₁ _
