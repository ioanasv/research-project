module lib.Haskell.ListSort where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.List

sort : {{ Ord a }} -> List a -> List a 
sort [] = []
sort (x ∷ []) = x ∷ []
sort {a} (x ∷ xs@(_ ∷ _)) = insert (sort xs)
    where 
      insert : List a -> List a 
      insert [] = x ∷ []
      insert (y ∷ ys) = if_then_else_ (x < y) (x ∷ y ∷ ys) (y ∷ (insert ys))