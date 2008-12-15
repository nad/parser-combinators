------------------------------------------------------------------------
-- Imports every module so that it is easy to see if everything builds
------------------------------------------------------------------------

module Everything where

import Parallel
import Parallel.Examples
import Parallel.Index
import Parallel.Lib
import RecursiveDescent.Coinductive
import RecursiveDescent.Coinductive.Examples
import RecursiveDescent.Coinductive.Internal
import RecursiveDescent.Coinductive.Lib
import RecursiveDescent.Hybrid
import RecursiveDescent.Hybrid.Examples
import RecursiveDescent.Hybrid.Lib
-- import RecursiveDescent.Hybrid.Memoised  -- Agda is too slow...
import RecursiveDescent.Hybrid.Memoised.Monad
import RecursiveDescent.Hybrid.Mixfix
  hiding (module Expr)  -- Necessary due to an Agda bug.
import RecursiveDescent.Hybrid.Mixfix.Example
import RecursiveDescent.Hybrid.Mixfix.Expr
import RecursiveDescent.Hybrid.Mixfix.Fixity
import RecursiveDescent.Hybrid.PBM
import RecursiveDescent.Hybrid.Simple
import RecursiveDescent.Hybrid.Type
import RecursiveDescent.Index
import RecursiveDescent.Inductive
import RecursiveDescent.Inductive.Char
import RecursiveDescent.Inductive.Examples
import RecursiveDescent.Inductive.Internal
import RecursiveDescent.Inductive.Lib
import RecursiveDescent.Inductive.Semantics
import RecursiveDescent.Inductive.SimpleLib
import RecursiveDescent.Inductive.Token
import RecursiveDescent.InductiveWithFix
import RecursiveDescent.InductiveWithFix.Examples
import RecursiveDescent.InductiveWithFix.Internal
import RecursiveDescent.InductiveWithFix.Lib
import RecursiveDescent.InductiveWithFix.PBM
import Utilities
