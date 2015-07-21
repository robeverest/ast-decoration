{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
module Eval where

import AST

-- Evaluation
-- ==============================================================
--
-- Evaluation of the simply type lambda calculus. Mostly for testing purposes.
--

prj :: Env env -> Idx env t -> t
prj BaseEnv _ = error "Unreachable"
prj (PushEnv s env) ZeroIdx      = s
prj (PushEnv s env) (SuccIdx ix) = prj env ix

evalPreOpenSTLC
  :: (forall env' t. Env env' -> stlc env' t -> t)
  -> Env env
  -> PreOpenSTLC stlc env t
  -> t
evalPreOpenSTLC eval env stlc =
  case stlc of
    Var ix       -> prj env ix
    Lam s        -> \a -> eval (PushEnv a env) s
    App a b      -> eval env a $ eval env b
    Let bnd body -> eval (PushEnv (eval env bnd) env) body
    Constant c      -> c

evalOpenSTLC :: Env env -> OpenSTLC env t -> t
evalOpenSTLC env (OpenSTLC stlc) = evalPreOpenSTLC evalOpenSTLC env stlc
