{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}
module Rewrite where

import Prelude          hiding ( id )
import AST
import Substitution

import Data.Functor
import Data.Typeable
import Data.Monoid

-- A conditional rewrite rule. Rather than having a boolean condition, the
-- condition gives a proof object which the RHS has access to.
data Rule env where
  Rule ::
          -- The condition
          (forall proxy env a t. (Typeable a, Typeable t)
            => OpenSTLC env a          -- The term captured by the metavariable
            -> OpenSTLC env t          -- The whole term matched
            -> Maybe (c a t))          -- The proof object the RHS can use.

          -- LHS: For the purposes of matching, we actually don't care what the
          -- type of 'a' is.
       -> OpenSTLC (a ': env) t

          -- RHS: Completely polymorphic. Takes the proof object from the
          -- condition which can allow constraints to be placed on the type.
       -> (forall a t. (Typeable a, Typeable t)
            => c a t -> OpenSTLC (a ': env) t)
       -> Rule env

-- Index matching.
--
matchIdx :: Idx env t -> Idx env t' -> Maybe (t :~: t')
matchIdx ZeroIdx      ZeroIdx       = Just Refl
matchIdx (SuccIdx ix) (SuccIdx ix') | Just Refl <- matchIdx ix ix'
                                    = Just Refl
matchIdx _            _             = Nothing

-- An intermediate result of trying to match a rule.
data Match c where
  NoMatch  :: Match c      -- Terms don't match

  Match    :: Match c      -- Terms do match, but the meta variable has yet to
                           -- be assigned.
  Assigned :: Typeable a
           => c a
           -> Match c      -- Terms match and have assignment for variable.


instance Show (Match (OpenSTLC env)) where
  show NoMatch      = "NoMatch"
  show Match        = "Match"
  show (Assigned _) = "Assigned"

instance Monoid (Match c) where
  mempty = Match

  NoMatch    `mappend` m          = NoMatch
  m          `mappend` NoMatch    = NoMatch
  Match      `mappend` m          = m
  m          `mappend` Match      = m
  Assigned _ `mappend` Assigned _ = error "Variable appears twice on LHS"

-- NB: The condition that a metavariable doesb't appear twice on the LHS is not
-- strictly needed. We could very easily just try to match the two assignments
-- for equality. I've just left this out for simplicity.

-- Actually do the rewriting.
--
rewrite :: forall env t. Typeable t => Rule env -> OpenSTLC env t -> OpenSTLC env t
rewrite rule@(Rule cond lhs rhs) term@(OpenSTLC stlc) =
  let
    term' = OpenSTLC (descend stlc) -- First descend further down the term
                                    -- (bottom up rewriting).
  in case unify Here lhs term of    -- ... then try to match the lhs of the rule.
    Assigned t
      | Just c <- cond t term       -- Have match. Need to check the condition
      -> inline (rhs c) t
    _ -> term'
  where
    descend :: PreOpenSTLC OpenSTLC env t -> PreOpenSTLC OpenSTLC env t
    descend (App a b)    = App (rewrite rule a) (rewrite rule b)
    descend (Lam a)      = Lam (rewrite (weakenRule rule) a)
    descend (Let a b)    = Let (rewrite rule a) (rewrite (weakenRule rule) b)
    descend t@Var{}      = t
    descend t@Constant{} = t

    weakenRule :: Rule env -> Rule (a ': env)
    weakenRule (Rule cond lhs rhs) = Rule cond (weaken ixt lhs) (weaken ixt . rhs)
      where
        ixt :: Idx (a' ': env) t' -> Idx (a' ': a ': env) t'
        ixt ZeroIdx = ZeroIdx
        ixt (SuccIdx ix) = SuccIdx (SuccIdx ix)

-- Captures where the metavariable exists in the environtment.
-- 'env' is the environment before the meta variable, 'env'' is the environment
-- including 'a' and 'env''' is the environment without a.
--
data InEnv a env env' env'' where
  Here  :: InEnv a env (a ': env) env
  There :: InEnv a env env' env'' -> InEnv a env (t1 ': env') (t2 ': env'')

-- Try to unify the LHS of the rule with some term. Note that we ignore the type
-- of the LHS for the purposes of matching.
--
unify :: Typeable t'
      => InEnv a env env' env''
      -> OpenSTLC env'  t       -- LHS
      -> OpenSTLC env'' t'      -- The term we hope to unify with
      -> Match (OpenSTLC env)   -- The match for the single metavariable.
unify x (OpenSTLC lhs) (OpenSTLC term) = unify' x lhs term
  where
    unify' :: Typeable t'
           => InEnv a env env' env''
           -> PreOpenSTLC OpenSTLC env'  t
           -> PreOpenSTLC OpenSTLC env'' t'
           -> Match (OpenSTLC env)
    unify' x (Var ix) t | isIn x ix
      = maybe NoMatch Assigned $ strengthen (strEnv x) (OpenSTLC t)
    unify' x (Var ix) (Var ix')
      | sameIdx x ix ix'
      = Match
    unify' x (App a b)    (App a' b')  = unify x a a' <> unify x b b'
    unify' x (Lam a)      (Lam a')     = unify (There x) a a'
    unify' x (Let a b)    (Let a' b')  = unify x a a' <> unify (There x) b b'
    unify' x (Constant a) (Constant b) | maybe False (a ==) (cast b)
                                       = Match
    unify' _ _            _            = NoMatch

    -- We want to know if the two indices are the same, but we don't care if
    -- their types match.
    sameIdx :: InEnv a env env' env'' -> Idx env' t -> Idx env'' t' -> Bool
    sameIdx Here      ZeroIdx      _
      = False
    sameIdx Here      (SuccIdx ix) ix'
      | Just Refl <- matchIdx ix ix'
      = True
    sameIdx (There x) ZeroIdx      ZeroIdx
      = True
    sameIdx (There x) (SuccIdx ix) (SuccIdx ix')
      = sameIdx x ix ix'
    sameIdx _ _            _
      = False

    isIn :: InEnv a env env' env'' -> Idx env' t' -> Bool
    isIn Here      ZeroIdx      = True
    isIn (There x) (SuccIdx ix) = isIn x ix
    isIn _         _            = False

    strEnv :: InEnv a env env' env'' -> env'' :?> env
    strEnv Here ix                = Just ix
    strEnv (There _) ZeroIdx      = Nothing
    strEnv (There x) (SuccIdx ix) = strEnv x ix

-- Some smart AST contstructors for writing tests.
--
lam = OpenSTLC . Lam
app a b = OpenSTLC (App a b)
constant = OpenSTLC . Constant
var0 = OpenSTLC (Var ZeroIdx)
var1 = OpenSTLC (Var (SuccIdx ZeroIdx))
id = lam var0

-- Rewrite rule for applications of 'id' - i.e.
--
-- id a = a
--
-- Note the condition checks that the the type of the metavariable and the type
-- of the LHS of the rule are the same.
--
idElim :: Rule '[]
idElim = Rule (\_ _ -> eqT)

              -- Need to supply some type in order to satisfy the typeable
              -- constraint. This is slightly annoying, but I don't see a better
              -- solution.
              (id `app` (var0 :: OpenSTLC '[()] ()))

              (\Refl -> var0)

-- Rewrite rule that performs eta-elimination.
--
etaElim :: Rule '[]
etaElim = Rule (\_ _ -> eqT) (lam (var1 `app` var0) :: OpenSTLC '[() -> ()] (() -> ())) (\Refl -> var0)

-- Some simple tests.
--
test1 :: OpenSTLC '[] Int
test1 = id `app` constant 0

test2 :: OpenSTLC '[] (Int -> Int)
test2 = lam $ id `app` var0

test3 :: OpenSTLC env (Float -> Float)
test3 = (lam $ id `app` var0) `app` id

neg_neg :: Rule '[(Float -> Float)]
neg_neg = Rule (\_ _ -> eqT) (neg (neg var0)) (\Refl -> var0)
  where
    neg = app var1

test4 :: OpenSTLC ((Float -> Float)  ': env) ((Float -> Float -> Float) -> Float) 
test4 = lam $ neg (constant 0.0 `plus` neg (constant 1.0) `plus` constant 2.0 `plus` neg (neg (constant 3.0)))
  where
    neg  = app var1
    plus a b = app (app var0 a) b 