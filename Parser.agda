------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

module Parser where

open import Parser.Type public
import Parser.Internal as P
open P public using (Parser; Grammar)

open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Product.Record
import Data.Product as Prod
open import Data.Function
import Data.BoundedVec.Inefficient as BVec
open import Logic

------------------------------------------------------------------------
-- Run function for the parsers

parse :  forall {tok nt i r}
      -> Parser tok nt i r -> Grammar tok nt
      -> [ tok ] -> [ Prod._×_ r [ tok ] ]
parse p g s = map (Prod.map-× id BVec.toList)
                  (P.parse g p (BVec.fromList s))

-- A variant which only returns parses which leave no remaining input.

parse-complete :  forall {tok nt i r}
               -> Parser tok nt i r -> Grammar tok nt
               -> [ tok ] -> [ r ]
parse-complete p g s =
  map Prod.proj₁ (filter (null ∘ Prod.proj₂) (parse p g s))

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
                         else proj₂ i₁
           )

_∣I_ : Index -> Index -> Index
i₁ ∣I i₂ = (proj₁ i₁ ∨ proj₁ i₂ , node (proj₂ i₁) (proj₂ i₂))

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 40 _∣_
infixl 10 _>>=_

return : forall {tok nt r} -> r -> Parser tok nt 1I r
return = P.ret

sat : forall {tok nt r} ->
      (tok -> Maybe r) -> Parser tok nt 0I r
sat = P.sat

-- Forget whether or not the parser accepts the empty string; take the
-- safe route and pretend that the empty string is accepted. This can
-- be used to make some functions simply typed.

forget : forall {tok nt e c r} ->
         Parser tok nt (e , c) r ->
         Parser tok nt (true , c) r
forget p = P.forget _ p

_>>=_ : forall {tok nt e₁ c₁ i₂ r₁ r₂} -> let i₁ = (e₁ , c₁) in
      Parser tok nt i₁ r₁ ->
      (r₁ -> Parser tok nt i₂ r₂) ->
      Parser tok nt (i₁ ·I i₂) r₂
_>>=_ {e₁ = true } = P.bind₀
_>>=_ {e₁ = false} = P.bind₁ _

_∣_ : forall {tok nt e₁ c₁ i₂ r} -> let i₁ = (e₁ , c₁) in
      Parser tok nt i₁ r ->
      Parser tok nt i₂ r ->
      Parser tok nt (i₁ ∣I i₂) r
_∣_ {e₁ = true } = P.alt₀ _
_∣_ {e₁ = false} = P.alt₁

!_ : forall {tok nt e c r} ->
     nt (e , c) r -> Parser tok nt (e , step c) r
!_ = P.!_

------------------------------------------------------------------------
-- Casting the indices

cast : forall {tok nt e₁ c₁ e₂ c₂ r} ->
       e₁ ≡ e₂ -> c₁ ≡ c₂ ->
       Parser tok nt (e₁ , c₁) r -> Parser tok nt (e₂ , c₂) r
cast ≡-refl ≡-refl p = p
