{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE InstanceSigs       #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE UndecidableInstances #-}
module Decoration where

import Control.Applicative
import Control.Monad
import Data.Functor.Identity

import AST
import Substitution


-- Decoration
-- ========================================================
--
-- We want to be able to decorate the syntax tree with information during
-- optimisation and analysis. We want to do this in such a way that it is
-- general. That is, we can add extra annotations to one stage of the pipeline
-- without affecting subsequent and prior stages.
--

-- | A simple decoration that just adds a string to every node of the tree. This
-- could be useful for variable names in code generation.
--
data Labelled stlc env t = Labelled String (stlc env t)

-- | A more complex decoration that actually depends on the environment. In this
-- case, holding a count of the number of each variable in the contained term.
--
data Counted stlc env t
  = Counted (Env (Map (Const Int) env)) (stlc env t)

-- | A decoration that carries a proof of Show for the type of the term. This
-- enables pretty printing of a term without having to constrain the orignal
-- syntax to only contain 'Show'-able constants.
--
data Shown stlc env t where
  Shown :: Show t => stlc env t -> Shown stlc env t

data Subst stlc env t where
  Subst :: (forall t. Idx env' t -> InnerSyntax stlc env t)
       -> stlc env' t
       -> Subst stlc env t

-- | The most general form of a decoration. Instances should obey functor style
-- laws -- i.e. lift id = id, lift f (lift g) s = lift (f . g) s
--
class Decoration dec where
  lift :: (forall env t. stlc env t -> stlc' env t)
       -> dec stlc env t -> dec stlc' env t

instance Decoration Labelled where
  lift f (Labelled l stlc) = Labelled l (f stlc)

instance Decoration Counted where
  lift f (Counted c stlc) = Counted c (f stlc)

instance Decoration Shown where
  lift f (Shown stlc) = Shown (f stlc)

-- instance Decoration (Subst) where
--   lift f (Subst v stlc) = Subst v (f stlc)

instance Decoration PreOpenSTLC where
  lift f stlc =
    case stlc of
      Var ix       -> Var ix
      Lam s        -> Lam (f s)
      App a b      -> App (f a) (f b)
      Let bnd body -> Let (f bnd) (f body)
      Constant c   -> Constant c

-- | Decorations that may affect, or depend on, a term's environment, but which
-- do not affect or depend on its type.
--
class Decoration dec => Rebuilder dec where
  withRebuilder :: (forall env. stlc env t -> stlc env t')
                -> dec stlc env t
                -> dec stlc env t'

instance Rebuilder Labelled where
  withRebuilder f (Labelled l stlc) = Labelled l (f stlc)

instance Rebuilder Counted where
  withRebuilder f (Counted c stlc) = Counted c (f stlc)

-- Note the absence of an instance for Shown.

-- While this instance looks like it should work, it doesn't. The reason is that
-- 'Subst' depends on the syntax immediately below it in the hiearchy.
-- instance Rebuilder (Subst) where
--   withRebuilder f (Subst v stlc) = Subst v (f stlc)

-- | A decoration that preserves a terms context (environment), but may affect,
-- or depend on, its type.
--
class Decoration dec => Contextual dec where
  withContextual :: (forall t. stlc env t -> stlc env' t)
                 -> dec stlc env  t
                 -> dec stlc env' t

instance Contextual Labelled where
  withContextual f (Labelled l stlc) = Labelled l (f stlc)

instance Contextual Shown where
  withContextual f (Shown stlc) = Shown (f stlc)

-- | A decoration that does not depend on the type or environment of a term.
--
class (Rebuilder dec, Contextual dec) => Annotation dec where
  withAnnotation :: (stlc env t -> stlc env' t')
                 -> dec stlc env  t
                 -> dec stlc env' t'

instance Annotation Labelled where
  withAnnotation f (Labelled l stlc) = Labelled l (f stlc)

deferSubst :: (VarIn (InnerSyntax stlc), Sink stlc)
          => stlc env t
          -> Subst stlc env t
deferSubst stlc = Subst varIn stlc

instance (Sink (InnerSyntax stlc), Sink stlc) => Sink (Subst stlc) where
  weaken v (Subst v' stlc) = Subst (weaken v . v') stlc

deSubst :: forall inner stlc env t. (Rebuildable Identity stlc, Sink stlc)
       => Subst stlc env t
       -> stlc env t
deSubst (Subst v' stlc)
  = substitute v' stlc


type instance InnerSyntax (Subst stlc) = InnerSyntax stlc

instance (inner ~ InnerSyntax stlc, VarIn inner, Rebuildable Identity inner, InnerSyntax inner ~ inner)
  => Rebuildable Identity (Subst stlc) where
  reconstruct v (Subst v' stlc) = pure $ Subst (compSubstitution v' (runIdentity . v)) stlc

compSubstitution :: Rebuildable Identity stlc
                 => (forall t. Idx env  t -> stlc env' t)
                 -> (forall t. Idx env' t -> InnerSyntax stlc env'' t)
                 -> Idx env t
                 -> stlc env'' t
compSubstitution v w ix = substitute w (v ix)

-- A type level map.
--
type family Map f xs where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs