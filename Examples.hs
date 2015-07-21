{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Examples where

import Data.Functor
import Data.Functor.Identity

import AST
import Substitution
import Decoration

newtype LabelledSTLC env t
  = LabelledSTLC (Labelled (PreOpenSTLC LabelledSTLC) env t)

newtype SubstLabelledSTLC env t
  = SubstLabelledSTLC (Subst (Labelled (PreOpenSTLC SubstLabelledSTLC)) env t)

newtype SubstLabelledCountedSTLC env t
  = SubstLabelledCountedSTLC (Subst (Labelled (Counted (PreOpenSTLC SubstLabelledCountedSTLC))) env t)

newtype SubstSTLC env t = SubstSTLC { substStlc :: Subst (PreOpenSTLC SubstSTLC) env t }

newtype ShownSTLC env t = ShownSTLC { shownStlc :: Shown (PreOpenSTLC ShownSTLC) env t }

instance Sink SubstSTLC where
  weaken v (SubstSTLC stlc) = SubstSTLC $ weaken v stlc

type instance InnerSyntax SubstSTLC = PreOpenSTLC SubstSTLC

instance Rebuildable Identity SubstSTLC where
  reconstruct v (SubstSTLC stlc) = SubstSTLC <$> reconstruct v stlc

deSubstSTLC :: SubstSTLC env t
           -> OpenSTLC env t
deSubstSTLC = OpenSTLC . lift deSubstSTLC . deSubst . substStlc

-- Simple tests
-- ==========================================================================
--

test1 :: OpenSTLC '[] Int
test1 = OpenSTLC $ App (OpenSTLC (Lam (OpenSTLC (Var ZeroIdx)))) (OpenSTLC (Constant 1))

test2 :: OpenSTLC '[Int -> Int] Int
test2 = OpenSTLC $ Let (OpenSTLC $ Constant 2) (OpenSTLC $ App (OpenSTLC $ Var (SuccIdx ZeroIdx)) (OpenSTLC $ Var ZeroIdx))

test3 :: SubstLabelledCountedSTLC '[] Int
test3 = SubstLabelledCountedSTLC $ Subst noVar (Labelled "Fish" (Counted BaseEnv (Constant 0)))

noVar :: Idx '[] e -> a
noVar ix = case ix of { }

test4 :: SubstSTLC '[a, b, Int] Int
test4 = weaken SuccIdx (weaken SuccIdx (SubstSTLC (Subst Var (Var ZeroIdx))))