{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Substitution where

import Control.Applicative
import Data.Functor.Identity
import Data.Typeable

import AST

-- Rebuilding
-- =======================================================
--
-- Simultaneous substitution of the simply typed lambda calculus.
--
-- This takes a slightly different approach to McBride's technique in that it
-- does not have the notion of "stuff". That is to say, it does not rely on a
-- typeclass that captures the different forms of substitution (renaming or
-- inlining). It simply treats renaming as a specialisation of inlining. This
-- approach works, but is no longer trivially structurally recursive.
--
-- In addition to this, McBride's technique is further generalised to work over
-- an applicative. The advantage of this is it gives us strengthening as well
-- as weakening (see below).
--

-- A method for applying a substitution over a language. Given a function from an index in the environment to a term in the inner syntax (see below), perform substitution on a term in the outer syntax.
type Substitute stlc =
  forall env env' a.
       (forall a'. Typeable a' => Idx env a' -> InnerSyntax stlc env' a')
    -> stlc env  a
    -> stlc env' a

-- Effectful substitution. Like 'Substitute', but the supplied function carries some effect 'f'. This allows more interesting effects like partial substution or "strengthening"
type Rebuild f stlc =
  forall env env' a.
       (forall a'. Typeable a' => Idx env a' -> f (InnerSyntax stlc env' a'))
    -> stlc env  a
    -> f (stlc env' a)

-- When languages are constructed by adding decorations onto existing languages (see 'Decoration'), it becomes necessary to specify which "level" of the language variables actually appear. We call this the inner syntax.
type family InnerSyntax (stlc :: [*] -> * -> *) :: [*] -> * -> *

-- The class of all syntaxes where a term can be generated from a DeBruijn index with no other information.
class VarIn stlc where
  varIn :: Typeable t => Idx env t -> stlc env t

-- Syntaxes that can be rebuilt.
--
class (VarIn (InnerSyntax stlc)) => Rebuildable f stlc where
  reconstruct :: Rebuild f stlc

-- If a syntax can be rebuilt with 'Identity' then substution can be performed over it.
--
type Substitutable stlc = Rebuildable Identity stlc

substitute :: Substitutable stlc => Substitute stlc
substitute v = runIdentity . reconstruct (Identity . v)

-- Rebuilding for 'PreOpenSTLC'
-- -----------------------------

instance VarIn (PreOpenSTLC stlc) where
  varIn = Var

type instance InnerSyntax (PreOpenSTLC stlc) = PreOpenSTLC stlc

instance (InnerSyntax stlc ~ PreOpenSTLC stlc, Substitutable stlc, Rebuildable f stlc, Applicative f) => Rebuildable f (PreOpenSTLC stlc) where
  reconstruct v stlc =
    case stlc of
      Var ix       -> v ix
      Lam s        -> Lam <$> reconstruct (shift v) s
      App a b      -> App <$> reconstruct v a <*> reconstruct v b
      Let bnd body -> Let <$> reconstruct v bnd <*> reconstruct (shift v) body
      Constant c      -> pure (Constant c)

shift
  :: (Typeable t, Applicative f, VarIn stlc, Sink stlc)
  => (forall t'. Typeable t' => Idx env t' -> f (stlc env' t'))
  -> Idx          (s ': env)  t
  -> f   (stlc (s ': env') t)
shift v ZeroIdx      = pure $ varIn ZeroIdx
shift v (SuccIdx ix) = weaken SuccIdx <$> v ix

-- Rebuilding for 'OpenSTLC'
-- -------------------------

instance VarIn OpenSTLC where
  varIn = OpenSTLC . Var

type instance InnerSyntax OpenSTLC = PreOpenSTLC OpenSTLC

instance Applicative f => Rebuildable f OpenSTLC where
  reconstruct v (OpenSTLC stlc) = OpenSTLC <$> reconstruct v stlc

-- Weakening
-- =============================================================
--
-- Weakening is the process of changing a term's environment to one greater
-- than or equal in size to the original. Operationally, this means changing
-- the value of the debruijn indices in the term via a mapping. We capture
-- this mapping with 'env :> env'', which is a function from indices in 'env'
-- to indices in 'env''
--
-- The process of renaming debruijn indices in a term, naturally requires
-- traversal of the entire term. This feels like a weakness of our
-- representation. In other representations, weakening is either constant time
-- or not necessary. However, we can amortise the cost of weakening to be
-- constant time by delaying it and performing many weakenings in bulk.
-- See 'Decoration'.
--
type env :> env' = forall t. Idx env t -> Idx env' t

-- | All things that can be weakened. We keep this as a separate typeclass and
-- not just a function defined in terms of 'substitute' as there are instances
-- when something can be weakened but cannot be rebuilt.
--
class Sink stlc where
  weaken :: env :> env' -> stlc env t -> stlc env' t
  default weaken :: Substitutable stlc => env :> env' -> stlc env t -> stlc env' t
  weaken v = substitute (varIn . v)

instance Sink Idx where
  weaken v = v

-- Both of these instances can be defined in terms of substitute.
--
instance (Substitutable stlc, InnerSyntax stlc ~ PreOpenSTLC stlc) => Sink (PreOpenSTLC stlc) where
instance Sink OpenSTLC where


