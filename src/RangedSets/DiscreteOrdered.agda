module RangedSets.DiscreteOrdered where

open import Agda.Builtin.Nat as Nat hiding (_==_; _<_; _+_; _-_)
open import Agda.Builtin.Char
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import lib.Haskell.Char
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Num
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.Monoid
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative
open import Haskell.Prim.Int
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import lib.Haskell.Real
open import Haskell.Prim.Tuple
open import Haskell.Prim.Double
open import Haskell.Prim.Bounded

{-# FOREIGN AGDA2HS
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
import Data.Char
import Data.Ratio
#-}

record DiscreteOrdered (a : Set) ⦃ _ : Ord a ⦄ : Set where
    field
        adjacent : a → a → Bool
        adjacentBelow : a → Maybe a

open DiscreteOrdered ⦃ ... ⦄ public
{-# COMPILE AGDA2HS DiscreteOrdered class #-}

orderingFromInt : Int → Ordering
orderingFromInt n = if_then_else_ (n == 0) LT (if_then_else_ (n == 1) EQ GT)
{-# COMPILE AGDA2HS orderingFromInt #-}

boundedAdjacentBool : (x y : Bool) → Bool
boundedAdjacentBool x y = if_then_else_ (x < y) true false
{-# COMPILE AGDA2HS boundedAdjacentBool #-}

boundedBelowBool : (x : Bool) → Maybe Bool
boundedBelowBool x = if_then_else_ (x == false) Nothing (Just false)
{-# COMPILE AGDA2HS boundedBelowBool #-}

boundedAdjacentOrdering : (x y : Ordering) → Bool
boundedAdjacentOrdering x y = if_then_else_ (x < y && x < GT) ((fromEnum x) + 1 == (fromEnum y)) false
{-# COMPILE AGDA2HS boundedAdjacentOrdering #-}

boundedBelowOrdering : (x : Ordering) → Maybe Ordering
boundedBelowOrdering x = if_then_else_ (x == LT) Nothing (Just (orderingFromInt ((fromEnum x) - 1)))
{-# COMPILE AGDA2HS boundedBelowOrdering #-}

boundedAdjacentChar : (x y : Char) → Bool
boundedAdjacentChar x y = if_then_else_ (x < y && x /= '\1114111') (((fromEnum x) + 1) == fromEnum y) false
{-# COMPILE AGDA2HS boundedAdjacentChar #-}

boundedBelowChar : (x : Char) → Maybe Char
boundedBelowChar x = if_then_else_ (x == '\0') Nothing (Just (chr ((ord x) - 1)))
{-# COMPILE AGDA2HS boundedBelowChar #-}

boundedAdjacentInt : (x y : Int) → Bool
boundedAdjacentInt x y = if_then_else_ (x < y && x /= 9223372036854775807) (x + 1 == y) false
{-# COMPILE AGDA2HS boundedAdjacentInt #-}

boundedBelowInt : (x : Int) → Maybe Int
boundedBelowInt x = if_then_else_ (x == -9223372036854775808) Nothing (Just (x - 1))
{-# COMPILE AGDA2HS boundedBelowInt #-}

boundedAdjacentInteger : (x y : Integer) → Bool
boundedAdjacentInteger x y = ((fromEnum x) + 1 == (fromEnum y))
{-# COMPILE AGDA2HS boundedAdjacentInteger #-}

boundedBelowInteger : (x : Integer) → Maybe Integer
boundedBelowInteger x = Just (x - (intToInteger 1))
-- {-# COMPILE AGDA2HS boundedBelowInteger #-}
{-# FOREIGN AGDA2HS
boundedBelowInteger :: Integer -> Maybe Integer
boundedBelowInteger x = Just (x - toInteger 1)
#-}

constructTuple : ⦃ o : Ord a ⦄ → ⦃ o2 : Ord b ⦄ → ⦃ DiscreteOrdered b ⦃ o2 ⦄ ⦄ → a → Maybe b → Maybe (a × b)
constructTuple _ Nothing = Nothing
constructTuple a (Just value) = Just (a , value)
{-# COMPILE AGDA2HS constructTuple #-}

constructTriple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ o : Ord c ⦄ → ⦃ DiscreteOrdered c ⦃ o ⦄ ⦄ → a → b → Maybe c → Maybe (a × b × c)
constructTriple _ _ Nothing = Nothing
constructTriple a b (Just value) = Just (a , b , value)
{-# COMPILE AGDA2HS constructTriple #-}

constructQuadtruple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ Ord c ⦄ → ⦃ o : Ord d ⦄ → ⦃ DiscreteOrdered d ⦃ o ⦄ ⦄
                        → a → b → c → Maybe d → Maybe (Tuple (a ∷ b ∷ c ∷ d ∷ []))
constructQuadtruple _ _ _ Nothing = Nothing
constructQuadtruple a b c (Just value) = Just (a ∷ b ∷ c ∷ value ∷ [])
{-# COMPILE AGDA2HS constructQuadtruple #-}

instance
    isDiscreteOrderedBool : DiscreteOrdered Bool
    isDiscreteOrderedBool . adjacent = boundedAdjacentBool
    isDiscreteOrderedBool . adjacentBelow = boundedBelowBool
{-# COMPILE AGDA2HS isDiscreteOrderedBool #-}

instance
    isDiscreteOrderedOrdering : DiscreteOrdered Ordering
    isDiscreteOrderedOrdering . adjacent = boundedAdjacentOrdering
    isDiscreteOrderedOrdering . adjacentBelow = boundedBelowOrdering
{-# COMPILE AGDA2HS isDiscreteOrderedOrdering #-}

instance
    isDiscreteOrderedChar : DiscreteOrdered Char
    isDiscreteOrderedChar . adjacent = boundedAdjacentChar
    isDiscreteOrderedChar . adjacentBelow = boundedBelowChar
{-# COMPILE AGDA2HS isDiscreteOrderedChar #-}

instance
    isDiscreteOrderedInt : DiscreteOrdered Int
    isDiscreteOrderedInt . adjacent = boundedAdjacentInt
    isDiscreteOrderedInt . adjacentBelow = boundedBelowInt
{-# COMPILE AGDA2HS isDiscreteOrderedInt #-}

instance
    isDiscreteOrderedInteger : DiscreteOrdered Integer
    isDiscreteOrderedInteger . adjacent = boundedAdjacentInteger
    isDiscreteOrderedInteger . adjacentBelow = boundedBelowInteger
{-# COMPILE AGDA2HS isDiscreteOrderedInteger #-}

instance
    isDiscreteOrderedDouble : DiscreteOrdered Double
    isDiscreteOrderedDouble . adjacent x y = false
    isDiscreteOrderedDouble . adjacentBelow x = Nothing
{-# COMPILE AGDA2HS isDiscreteOrderedDouble #-}

instance
    isDiscreteOrderedList : ⦃ o : Ord a ⦄ → ⦃ ol : Ord (List a) ⦄ → DiscreteOrdered (List a) ⦃ ol ⦄
    isDiscreteOrderedList . adjacent x y = false
    isDiscreteOrderedList . adjacentBelow x = Nothing
{-# COMPILE AGDA2HS isDiscreteOrderedList #-}

instance
    isDiscreteOrderedRatio : ⦃ o : Ord a ⦄ → ⦃ Integral a ⦄ → ⦃ or : Ord (Ratio a )⦄ → DiscreteOrdered (Ratio a) ⦃ or ⦄
    isDiscreteOrderedRatio . adjacent x y = false
    isDiscreteOrderedRatio . adjacentBelow x = Nothing
{-# COMPILE AGDA2HS isDiscreteOrderedRatio #-}


instance
    isDiscreteOrderedTuple : ⦃ Ord a ⦄ → ⦃ o : Ord b ⦄ → ⦃ DiscreteOrdered b ⦃ o ⦄ ⦄ 
                            →  ⦃ ot : Ord (a × b) ⦄ → DiscreteOrdered (a × b) ⦃ ot ⦄
    isDiscreteOrderedTuple . adjacent (x1 , x2) (y1 , y2) = (x1 == y1) && (adjacent x2 y2)
    isDiscreteOrderedTuple . adjacentBelow (x1 , x2) = constructTuple x1 (adjacentBelow x2)
{-# COMPILE AGDA2HS isDiscreteOrderedTuple #-}

instance
    isDiscreteOrderedTriple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ o : Ord c ⦄ → ⦃ DiscreteOrdered c ⦃ o ⦄ ⦄ 
                                → ⦃ ot : Ord (a × b × c) ⦄ → DiscreteOrdered (a × b × c) ⦃ ot ⦄
    isDiscreteOrderedTriple . adjacent (x1 , x2 , x3) (y1 , y2 , y3) = (x1 == y1) && (x2 == y2) && (adjacent x3 y3)
    isDiscreteOrderedTriple . adjacentBelow (x1 , x2 , x3) = constructTriple x1 x2 (adjacentBelow x3)
{-# COMPILE AGDA2HS isDiscreteOrderedTriple #-}

instance
    isDiscreteOrderedQuadtruple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → ⦃ Ord c ⦄
                            → ⦃ o : Ord d ⦄ → ⦃ DiscreteOrdered d ⦃ o ⦄ ⦄
                            → ⦃ ot : Ord (Tuple (a ∷ b ∷ c ∷ d ∷ [])) ⦄ → DiscreteOrdered (Tuple (a ∷ b ∷ c ∷ d ∷ [])) ⦃ ot ⦄
    isDiscreteOrderedQuadtruple . adjacent (x1 ∷ x2 ∷ x3 ∷ x4 ∷ []) (y1 ∷ y2 ∷ y3 ∷ y4 ∷ []) = (x1 == y1) && (x2 == y2) && (x3 == y3) && (adjacent x4 y4)
    isDiscreteOrderedQuadtruple . adjacentBelow (x1 ∷ x2 ∷ x3 ∷ x4 ∷ []) = constructQuadtruple x1 x2 x3 (adjacentBelow x4)
{-# COMPILE AGDA2HS isDiscreteOrderedQuadtruple #-}
