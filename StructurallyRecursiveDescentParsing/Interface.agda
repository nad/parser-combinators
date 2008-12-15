------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

-- Use StructurallyRecursiveDescentParsing.Simple to actually run the
-- parsers.

module StructurallyRecursiveDescentParsing.Interface where

open import StructurallyRecursiveDescentParsing.Index
import StructurallyRecursiveDescentParsing.Type as P
open P public using (Parser; Grammar)

open import Data.Bool
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 40 _∣_
infixl 10 _>>=_ _!>>=_

!_ : forall {Tok NT e c R} ->
     NT (e ◇ c) R -> Parser Tok NT (e ◇ step c) R
!_ = P.!_

symbol : forall {Tok NT} -> Parser Tok NT 0I Tok
symbol = P.symbol

return : forall {Tok NT R} -> R -> Parser Tok NT 1I R
return = P.return

fail : forall {Tok NT R} -> Parser Tok NT 0I R
fail = P.fail

_>>=_ : forall {Tok NT e₁ c₁ i₂ R₁ R₂} -> let i₁ = (e₁ ◇ c₁) in
        Parser Tok NT i₁ R₁ ->
        (R₁ -> Parser Tok NT i₂ R₂) ->
        Parser Tok NT (i₁ ·I i₂) R₂
_>>=_ {e₁ = true } = P._?>>=_
_>>=_ {e₁ = false} = P._!>>=_

-- If the first parser is guaranteed to consume something, then the
-- second parser's index can depend on the result of the first parser.

_!>>=_ : forall {Tok NT c₁ R₁ R₂} {i₂ : R₁ -> Index} ->
         let i₁ = (false ◇ c₁) in
         Parser Tok NT i₁ R₁ ->
         ((x : R₁) -> Parser Tok NT (i₂ x) R₂) ->
         Parser Tok NT (i₁ ·I 1I) R₂
_!>>=_ = P._!>>=_

_∣_ : forall {Tok NT e₁ c₁ i₂ R} -> let i₁ = (e₁ ◇ c₁) in
      Parser Tok NT i₁ R ->
      Parser Tok NT i₂ R ->
      Parser Tok NT (i₁ ∣I i₂) R
_∣_ = P.alt _ _

cast : forall {Tok NT e₁ e₂ c₁ c₂ R} ->
       e₁ ≡ e₂ -> c₁ ≡ c₂ ->
       Parser Tok NT (e₁ ◇ c₁) R -> Parser Tok NT (e₂ ◇ c₂) R
cast ≡-refl ≡-refl p = p
