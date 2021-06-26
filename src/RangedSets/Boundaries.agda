module RangedSets.Boundaries where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq

open import RangedSets.DiscreteOrdered

{-# FOREIGN AGDA2HS
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
import RangedSets.DiscreteOrdered
#-}
{-# FOREIGN AGDA2HS
infix 4 />/
#-}

data Boundary (a : Set) ⦃ o : Ord a ⦄ ⦃ d : DiscreteOrdered a ⦄ : Set where
    BoundaryAbove    : a → Boundary a
    BoundaryBelow    : a → Boundary a
    BoundaryAboveAll : Boundary a
    BoundaryBelowAll : Boundary a

{-# COMPILE AGDA2HS Boundary #-}

above : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
        → Boundary a ⦃ o ⦄ → a → Bool
above (BoundaryAbove b) a    = a > b
above (BoundaryBelow b) a    = a >= b
above BoundaryAboveAll _     = false
above BoundaryBelowAll _     = true
{-# COMPILE AGDA2HS above #-}

infixr 4 _/>/_
_/>/_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → a → Boundary a ⦃ o ⦄ → Bool
_/>/_ x (BoundaryAbove b) = x > b
_/>/_ x (BoundaryBelow b) = x >= b
_/>/_ _ BoundaryAboveAll = false
_/>/_ _ BoundaryBelowAll = true
{-# COMPILE AGDA2HS _/>/_ #-}

instance
    isBoundaryEq : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Eq (Boundary a)
    isBoundaryEq . _==_ (BoundaryAbove b1) (BoundaryAbove b2) = (b1 == b2)
    isBoundaryEq . _==_ (BoundaryAbove b1) (BoundaryBelow b2) = if_then_else_ (b1 < b2 && (adjacent b1 b2)) true false
    isBoundaryEq . _==_ (BoundaryBelow b1) (BoundaryBelow b2) = (b1 == b2)
    isBoundaryEq . _==_ (BoundaryBelow b1) (BoundaryAbove b2) = if_then_else_ (b1 > b2 && (adjacent b2 b1)) true false
    isBoundaryEq . _==_ BoundaryAboveAll BoundaryAboveAll = true
    isBoundaryEq . _==_ BoundaryBelowAll BoundaryBelowAll = true
    isBoundaryEq . _==_ _ _ = false
{-# COMPILE AGDA2HS isBoundaryEq #-}

instance
    isBoundaryOrd : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Ord (Boundary a)
    isBoundaryOrd . compare (BoundaryAbove b1) (BoundaryAbove b2) = compare b1 b2
    isBoundaryOrd . compare (BoundaryAbove b1) (BoundaryBelow b2) = if_then_else_ (b1 < b2) (if_then_else_ (adjacent b1 b2) EQ LT) GT
    isBoundaryOrd . compare (BoundaryAbove b1) BoundaryAboveAll = LT
    isBoundaryOrd . compare (BoundaryAbove b1) BoundaryBelowAll = GT
    isBoundaryOrd . compare (BoundaryBelow b1) (BoundaryBelow b2) = compare b1 b2
    isBoundaryOrd . compare (BoundaryBelow b1) (BoundaryAbove b2) = if_then_else_ (b1 > b2) (if_then_else_ (adjacent b2 b1) EQ GT) LT
    isBoundaryOrd . compare (BoundaryBelow b1) BoundaryAboveAll = LT
    isBoundaryOrd . compare (BoundaryBelow b1) BoundaryBelowAll = GT
    isBoundaryOrd . compare BoundaryAboveAll BoundaryAboveAll = EQ
    isBoundaryOrd . compare BoundaryAboveAll _ = GT
    isBoundaryOrd . compare BoundaryBelowAll BoundaryBelowAll = EQ
    isBoundaryOrd . compare BoundaryBelowAll _ = LT
    isBoundaryOrd ._<_ x y = compare x y == LT
    isBoundaryOrd ._>_ x y = compare x y == GT
    isBoundaryOrd ._<=_ x BoundaryAboveAll = true   
    isBoundaryOrd ._<=_ BoundaryBelowAll y = true   
    isBoundaryOrd ._<=_ x y = (compare x y == LT) || (compare x y == EQ)
    isBoundaryOrd ._>=_ x y = (compare x y == GT) || (compare x y == EQ)
    isBoundaryOrd .max x y = if (compare x y == GT) then x else y
    isBoundaryOrd .min x y = if (compare x y == LT) then x else y
{-# COMPILE AGDA2HS isBoundaryOrd #-}
