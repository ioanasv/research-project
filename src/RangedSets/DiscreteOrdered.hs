{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module RangedSets.DiscreteOrdered where



import Data.Char
import Data.Ratio

class DiscreteOrdered a where
    adjacent :: a -> a -> Bool
    adjacentBelow :: a -> Maybe a

orderingFromInt :: Int -> Ordering
orderingFromInt n
  = if n == 0 then LT else if n == 1 then EQ else GT

boundedAdjacentBool :: Bool -> Bool -> Bool
boundedAdjacentBool x y = if x < y then True else False

boundedBelowBool :: Bool -> Maybe Bool
boundedBelowBool x = if x == False then Nothing else Just False

boundedAdjacentOrdering :: Ordering -> Ordering -> Bool
boundedAdjacentOrdering x y
  = if x < y && x < GT then fromEnum x + 1 == fromEnum y else False

boundedBelowOrdering :: Ordering -> Maybe Ordering
boundedBelowOrdering x
  = if x == LT then Nothing else
      Just (orderingFromInt (fromEnum x - 1))

boundedAdjacentChar :: Char -> Char -> Bool
boundedAdjacentChar x y
  = if x < y && not (x == '\1114111') then
      fromEnum x + 1 == fromEnum y else False

boundedBelowChar :: Char -> Maybe Char
boundedBelowChar x
  = if x == '\NUL' then Nothing else Just (chr (ord x - 1))

boundedAdjacentInt :: Int -> Int -> Bool
boundedAdjacentInt x y
  = if x < y && not (x == 9223372036854775807) then x + 1 == y else
      False

boundedBelowInt :: Int -> Maybe Int
boundedBelowInt x
  = if x == (-9223372036854775808) then Nothing else Just (x - 1)

boundedAdjacentInteger :: Integer -> Integer -> Bool
boundedAdjacentInteger x y = fromEnum x + 1 == fromEnum y

boundedBelowInteger :: Integer -> Maybe Integer
boundedBelowInteger x = Just (x - toInteger 1)

constructTuple ::
                 Ord a => Ord b => DiscreteOrdered b => a -> Maybe b -> Maybe (a, b)
constructTuple _ Nothing = Nothing
constructTuple a (Just value) = Just (a, value)

constructTriple ::
                  Ord a =>
                    Ord b =>
                      Ord c => DiscreteOrdered c => a -> b -> Maybe c -> Maybe (a, b, c)
constructTriple _ _ Nothing = Nothing
constructTriple a b (Just value) = Just (a, b, value)

constructQuadtruple ::
                      Ord a =>
                        Ord b =>
                          Ord c =>
                            Ord d =>
                              DiscreteOrdered d => a -> b -> c -> Maybe d -> Maybe (a, b, c, d)
constructQuadtruple _ _ _ Nothing = Nothing
constructQuadtruple a b c (Just value) = Just (a, b, c, value)

instance DiscreteOrdered Bool where
    adjacent = boundedAdjacentBool
    adjacentBelow = boundedBelowBool

instance DiscreteOrdered Ordering where
    adjacent = boundedAdjacentOrdering
    adjacentBelow = boundedBelowOrdering

instance DiscreteOrdered Char where
    adjacent = boundedAdjacentChar
    adjacentBelow = boundedBelowChar

instance DiscreteOrdered Int where
    adjacent = boundedAdjacentInt
    adjacentBelow = boundedBelowInt

instance DiscreteOrdered Integer where
    adjacent = boundedAdjacentInteger
    adjacentBelow = boundedBelowInteger

instance DiscreteOrdered Double where
    adjacent x y = False
    adjacentBelow x = Nothing

instance (Ord a, Ord [a]) => DiscreteOrdered ([a]) where
    adjacent x y = False
    adjacentBelow x = Nothing

instance (Ord a, Integral a, Ord (Ratio a)) =>
         DiscreteOrdered (Ratio a)
         where
    adjacent x y = False
    adjacentBelow x = Nothing

instance (Ord a, Ord b, DiscreteOrdered b, Ord (a, b)) =>
         DiscreteOrdered ((a, b))
         where
    adjacent (x1, x2) (y1, y2) = x1 == y1 && adjacent x2 y2
    adjacentBelow (x1, x2) = constructTuple x1 (adjacentBelow x2)

instance (Ord a, Ord b, Ord c, DiscreteOrdered c, Ord (a, b, c)) =>
         DiscreteOrdered ((a, b, c))
         where
    adjacent (x1, x2, x3) (y1, y2, y3)
      = x1 == y1 && x2 == y2 && adjacent x3 y3
    adjacentBelow (x1, x2, x3)
      = constructTriple x1 x2 (adjacentBelow x3)

instance (Ord a, Ord b, Ord c, Ord d, DiscreteOrdered d,
          Ord (a, b, c, d)) =>
         DiscreteOrdered ((a, b, c, d))
         where
    adjacent (x1, x2, x3, x4) (y1, y2, y3, y4)
      = x1 == y1 && x2 == y2 && x3 == y3 && adjacent x4 y4
    adjacentBelow (x1, x2, x3, x4)
      = constructQuadtruple x1 x2 x3 (adjacentBelow x4)

