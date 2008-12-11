------------------------------------------------------------------------
-- Imports just the recommended modules
------------------------------------------------------------------------

module Recommended where

import RecursiveDescent.Hybrid
import RecursiveDescent.Hybrid.Examples
import RecursiveDescent.Hybrid.Lib
import RecursiveDescent.Hybrid.Mixfix
  hiding (module Expr)  -- Necessary due to an Agda bug.
import RecursiveDescent.Hybrid.Mixfix.Example
import RecursiveDescent.Hybrid.Mixfix.Expr
import RecursiveDescent.Hybrid.Mixfix.Fixity
import RecursiveDescent.Hybrid.PBM
import RecursiveDescent.Hybrid.Simple
import RecursiveDescent.Hybrid.Type
import RecursiveDescent.Index
import Utilities
