{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module RangedSets.Boundaries where



import RangedSets.DiscreteOrdered

infix 4 />/

data Boundary a = BoundaryAbove a
                | BoundaryBelow a
                | BoundaryAboveAll
                | BoundaryBelowAll

above :: Ord a => DiscreteOrdered a => Boundary a -> a -> Bool
above (BoundaryAbove b) a = a > b
above (BoundaryBelow b) a = a >= b
above BoundaryAboveAll _ = False
above BoundaryBelowAll _ = True

(/>/) :: Ord a => DiscreteOrdered a => a -> Boundary a -> Bool
x />/ BoundaryAbove b = x > b
x />/ BoundaryBelow b = x >= b
_ />/ BoundaryAboveAll = False
_ />/ BoundaryBelowAll = True

instance (Ord a, DiscreteOrdered a) => Eq (Boundary a) where
    BoundaryAbove b1 == BoundaryAbove b2 = b1 == b2
    BoundaryAbove b1 == BoundaryBelow b2
      = if b1 < b2 && adjacent b1 b2 then True else False
    BoundaryBelow b1 == BoundaryBelow b2 = b1 == b2
    BoundaryBelow b1 == BoundaryAbove b2
      = if b1 > b2 && adjacent b2 b1 then True else False
    BoundaryAboveAll == BoundaryAboveAll = True
    BoundaryBelowAll == BoundaryBelowAll = True
    _ == _ = False

instance (Ord a, DiscreteOrdered a) => Ord (Boundary a) where
    compare (BoundaryAbove b1) (BoundaryAbove b2) = compare b1 b2
    compare (BoundaryAbove b1) (BoundaryBelow b2)
      = if b1 < b2 then if adjacent b1 b2 then EQ else LT else GT
    compare (BoundaryAbove b1) BoundaryAboveAll = LT
    compare (BoundaryAbove b1) BoundaryBelowAll = GT
    compare (BoundaryBelow b1) (BoundaryBelow b2) = compare b1 b2
    compare (BoundaryBelow b1) (BoundaryAbove b2)
      = if b1 > b2 then if adjacent b2 b1 then EQ else GT else LT
    compare (BoundaryBelow b1) BoundaryAboveAll = LT
    compare (BoundaryBelow b1) BoundaryBelowAll = GT
    compare BoundaryAboveAll BoundaryAboveAll = EQ
    compare BoundaryAboveAll _ = GT
    compare BoundaryBelowAll BoundaryBelowAll = EQ
    compare BoundaryBelowAll _ = LT
    x < y = compare x y == LT
    x > y = compare x y == GT
    x <= BoundaryAboveAll = True
    BoundaryBelowAll <= y = True
    x <= y = compare x y == LT || compare x y == EQ
    x >= y = compare x y == GT || compare x y == EQ
    max x y = if compare x y == GT then x else y
    min x y = if compare x y == LT then x else y

