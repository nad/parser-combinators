------------------------------------------------------------------------
-- A library of parser combinators
------------------------------------------------------------------------

module Parallel.Lib where

open import Utilities
open import Parallel
open import Parallel.Index

open import Data.Bool
open import Data.Nat hiding (_≟_)
open import Data.Product.Record using (_,_)
open import Data.Product renaming (_,_ to pair)
open import Data.List
open import Data.Function
open import Data.Maybe
import Data.Char as C
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Applicative functor parsers

-- We could get these for free with better library support.

infixl 4 _⊛_ _<⊛_ _⊛>_ _<$>_ _<$_

-- Parser together with return and _⊛_ form a (generalised)
-- applicative functor. (Warning: I have not checked that the laws are
-- actually satisfied.)

-- Note that all the resulting indices can be inferred.

_⊛_ : forall {tok r₁ r₂ i₁ i₂} ->
      Parser tok i₁ (r₁ -> r₂) -> Parser tok i₂ r₁ ->
      Parser tok _ r₂ -- (i₁ ·I (i₂ ·I 1I))
f ⊛ x = f >>= \f' -> x >>= \x' -> return (f' x')

_<$>_ : forall {tok r₁ r₂ i} ->
        (r₁ -> r₂) -> Parser tok i r₁ -> Parser tok _ r₂ -- (i ·I 1I)
f <$> x = return f ⊛ x

_<⊛_ : forall {tok i₁ i₂ r₁ r₂} ->
       Parser tok i₁ r₁ -> Parser tok i₂ r₂ -> Parser tok _ r₁
x <⊛ y = const <$> x ⊛ y

_⊛>_ : forall {tok i₁ i₂ r₁ r₂} ->
       Parser tok i₁ r₁ -> Parser tok i₂ r₂ -> Parser tok _ r₂
x ⊛> y = flip const <$> x ⊛ y

_<$_ : forall {tok r₁ r₂ i} ->
       r₁ -> Parser tok i r₂ -> Parser tok _ r₁
x <$ y = const x <$> y

------------------------------------------------------------------------
-- Parsers for sequences

mutual

  _⋆ : forall {tok r d} ->
       Parser tok (false , d) r     ->
       Parser tok _           [ r ]
  p ⋆ ~ return [] ∣ p +

  _+ : forall {tok r d} ->
       Parser tok (false , d) r     ->
       Parser tok (false , d) [ r ]
  p + ~ _∷_ <$> p ⊛ p ⋆

  -- Are these definitions productive? _∣_ and _⊛_ are not
  -- constructors... Unfolding (and ignoring some casts) we get
  -- (unless I've made some mistake)
  --
  --   p ⋆ ~ parser \k -> Base._∣_ (k []) (unP (p +) k)
  --
  -- and
  --
  --   p + ~ parser (\k -> unP p     (\x  ->
  --                       unP (p ⋆) (\xs -> k (x ∷ xs))))
  --       ~ parser (\k -> unP p     (\x  -> Base._∣_ (k (x ∷ []))
  --                      (unP (p +) (\xs -> k (x ∷ xs))))).
  --
  -- Assume that p + is applied to the continuation k =
  -- const Base.fail. We get
  --
  --   unP (p +) k ~ unP p (\_ -> unP (p +) k).
  --
  -- This implies that the definitions above are not /obviously/
  -- productive. Note now that when p is defined the function unP p
  -- has type
  --
  --   forall {i' r'} ->
  --   (r -> Base.Parser tok r' i') ->
  --   Base.Parser tok r' (i ·I i')
  --
  -- for arbitrary i' and r', and with i = (false , d) as above this
  -- specialises to
  --
  --   forall {i' r'} ->
  --   (r -> Base.Parser tok r' i') ->
  --   Base.Parser tok r' (false , d).
  --
  -- Due to parametricity p cannot make use of the result of the
  -- continuation to build the resulting value, so the only way to
  -- build the result is to use a constructor (either directly or via
  -- a productive function). However, if p can pattern match on the
  -- result of the continuation (like in Parallel.problematic), then
  -- unP (p +) is not productive. In this case the module system
  -- prevents p from performing such pattern matching /directly/, but
  -- ensuring that this is not possible /indirectly/ seems overly
  -- difficult, considering that there are definitions (other than
  -- Parallel.problematic) which pattern match on Base.Parser.
  --
  -- As an example the type checking of the following definition does
  -- not terminate:
  --
  --   loops : parse-complete (problematic false + >>= \_ -> fail) ('a' ∷ [])
  --           ≡ []
  --   loops = ≡-refl
  --
  -- Furthermore the definition of number below, which uses _+, is
  -- rather fragile, and the type checking of some definitions in
  -- Parallel.Examples which use number fail to terminate (at least
  -- with the version of Agda which is current at the time of
  -- writing).

-- p sepBy sep parses one or more ps separated by seps.

_sepBy_ : forall {tok r r' i d} ->
          Parser tok i r -> Parser tok (false , d) r' ->
          Parser tok _ [ r ]
p sepBy sep = _∷_ <$> p ⊛ (sep ⊛> p) ⋆

chain₁ :  forall {tok d₁ i₂ r}
       -> Assoc
       -> Parser tok (false , d₁) r
       -> Parser tok i₂ (r -> r -> r)
       -> Parser tok _ r
chain₁ a p op = chain₁-combine a <$> (pair <$> p ⊛ op) ⋆ ⊛ p

chain :  forall {tok d₁ i₂ r}
      -> Assoc
      -> Parser tok (false , d₁) r
      -> Parser tok i₂ (r -> r -> r)
      -> r
      -> Parser tok _ r
chain a p op x = return x ∣ chain₁ a p op

------------------------------------------------------------------------
-- Parsing a given token (symbol)

module Sym (a : DecSetoid) where

  open DecSetoid a using (_≟_) renaming (carrier to tok)

  sym : tok -> Parser tok _ tok
  sym x = sat p
    where
    p : tok -> Maybe tok
    p y with x ≟ y
    ... | yes _ = just y
    ... | no  _ = nothing

------------------------------------------------------------------------
-- Character parsers

digit : Parser C.Char _ ℕ
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
  where open Sym C.decSetoid

number : Parser C.Char _ ℕ
number = toNum <$> ds
  where
  -- Inlining ds makes the type checker loop.
  ds = digit +

  toNum = foldr (\n x -> 10 * x + n) 0 ∘ reverse
