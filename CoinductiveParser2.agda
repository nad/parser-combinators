------------------------------------------------------------------------
-- Terminating parser combinator interface
------------------------------------------------------------------------

module CoinductiveParser2 where

open import Parser.Type public
import CoinductiveParser2.Internal as P
open P public using (Parser)

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec
open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Run function for the parsers

parse : forall {tok i r} ->
        Parser tok i r -> [ tok ] -> [ Prod._×_ r [ tok ] ]
parse p s = map (Prod.map-× id BVec.toList)
                (P.parse p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete : forall {tok i r} ->
                 Parser tok i r -> [ tok ] -> [ r ]
parse-complete p s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p s))

------------------------------------------------------------------------
-- Operations on indices

infixr 50 _·I_
infixr 40 _∣I_

0I : Index
0I = (false , leaf)

1I : Index
1I = (true , leaf)

_·I_ : Index -> Index -> Index
i₁ ·I i₂ = ( proj₁ i₁ ∧ proj₁ i₂
           , if proj₁ i₁ then node (proj₂ i₁) (proj₂ i₂)
                         else step (proj₂ i₁)
           )

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = (proj₁ i₁ ∨ proj₁ i₂ , node (proj₂ i₁) (proj₂ i₂))

------------------------------------------------------------------------
-- Exported combinators

infixl 50 _⊛_
infixl 40 _∣_

return : forall {tok r} -> r -> Parser tok 1I r
return = P.ret

sat : forall {tok r} -> (tok -> Maybe r) -> Parser tok 0I r
sat = P.sat

-- Forget whether or not the parser accepts the empty string; take the
-- safe route and pretend that the empty string is accepted. This can
-- be used to make some functions simply typed.

forget : forall {tok e c r} ->
         Parser tok (e , c) r ->
         Parser tok (true , step c) r
forget p = P.forget _ p

_⊛_ : forall {tok e₁ c₁ i₂ r₁ r₂} -> let i₁ = (e₁ , c₁) in
      Parser tok i₁ (r₁ -> r₂) ->
      Parser tok i₂ r₁ ->
      Parser tok (i₁ ·I i₂) r₂
_⊛_ {e₁ = true } = P.seq₀
_⊛_ {e₁ = false} = P.seq₁ _

_∣_ : forall {tok e₁ c₁ i₂ r} -> let i₁ = (e₁ , c₁) in
      Parser tok i₁ r ->
      Parser tok i₂ r ->
      Parser tok (i₁ ∣I i₂) r
_∣_ {e₁ = true } = P.alt₀ _
_∣_ {e₁ = false} = P.alt₁
