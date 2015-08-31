{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

module AST where

import Data.Typeable

-- The core calculus
-- ========================================================
--
-- This is a definition of the simply typed lambda calculus with let expressions and constants.
--
-- We use this as the core calculus for experimenting with programs transformation and decoration. However, for the most part, these experiments are parameterised by the language the operate over, so the choice of this calculus is purely for illustration purposes.
--

-- Indices into an environment, which we model as a type-level list.
--
data Idx env t where
  ZeroIdx :: Idx (t ': env) t
  SuccIdx :: Idx env t -> Idx (a ': env) t

deriving instance Show (Idx env t)

-- A value level reflection of an environment.
--
data Env env where
  BaseEnv :: Env '[]
  PushEnv :: s -> Env env -> Env (s ': env)

-- The actual AST itself. We make this an open data type by passing a continuation instead of making it recursive.
--
data PreOpenSTLC stlc (env :: [*]) t where
  Var :: Typeable t
      => Idx env t
      -> PreOpenSTLC stlc env t

  Lam :: (Typeable a, Typeable t)
      => stlc (a ': env) t
      -> PreOpenSTLC stlc env (a -> t)

  App :: (Typeable a, Typeable t)
      => stlc env (a -> t)
      -> stlc env a
      -> PreOpenSTLC stlc env t

  Let :: (Typeable a, Typeable t)
      => stlc env a
      -> stlc (a ': env) t
      -> PreOpenSTLC stlc env t

  Constant :: (Eq t, Typeable t)
           => t
           -> PreOpenSTLC stlc env t

-- The simplest version of the calculus. Here we just "tie the recursive knot" to get the language we desire.
--
newtype OpenSTLC env t = OpenSTLC (PreOpenSTLC OpenSTLC env t)
