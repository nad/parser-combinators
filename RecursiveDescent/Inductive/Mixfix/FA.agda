------------------------------------------------------------------------
-- Fixity and associativity
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.FA where

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Fin.Props using (eq?)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Fixities

data Fixity : Set where
  prefx  : Fixity
  infx   : Fixity -- infix is a reserved word.
  postfx : Fixity
  closed : Fixity

data Associativity : Set where
  left  : Associativity
  right : Associativity
  non   : Associativity

-- A combination of fixity and associativity. Only infix operators
-- have associativity.

data FA : Set where
  prefx  : FA
  infx   : (assoc : Associativity) -> FA
  postfx : FA
  closed : FA

fixity : FA -> Fixity
fixity prefx    = prefx
fixity (infx _) = infx
fixity postfx   = postfx
fixity closed   = closed

FA-is-finite : LeftInverse FA (Fin 6)
FA-is-finite = record
  { from         = from
  ; to           = to
  ; left-inverse = left-inverse
  }
  where
  to : FA -> Fin 6
  to prefx        = # 0
  to (infx left)  = # 1
  to (infx right) = # 2
  to (infx non)   = # 3
  to postfx       = # 4
  to closed       = # 5

  from : Fin 6 -> FA
  from zero                                   = prefx
  from (suc zero)                             = infx left
  from (suc (suc zero))                       = infx right
  from (suc (suc (suc zero)))                 = infx non
  from (suc (suc (suc (suc zero))))           = postfx
  from (suc (suc (suc (suc (suc zero)))))     = closed
  from (suc (suc (suc (suc (suc (suc ()))))))

  left-inverse : from LeftInverseOf to
  left-inverse prefx        = ≡-refl
  left-inverse (infx left)  = ≡-refl
  left-inverse (infx right) = ≡-refl
  left-inverse (infx non)   = ≡-refl
  left-inverse postfx       = ≡-refl
  left-inverse closed       = ≡-refl

_≟_ : Decidable (_≡_ {FA})
_≟_ = eq? injection
  where open LeftInverse FA-is-finite
