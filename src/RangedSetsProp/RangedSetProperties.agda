module RangedSetsProp.RangedSetProperties where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Haskell.Prim
open import Haskell.Prim.Ord
open import lib.Haskell.ListSort
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Eq
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Double
open import Haskell.Prim.Foldable

open import RangedSets.DiscreteOrdered
open import RangedSets.Boundaries
open import RangedSets.Ranges
open import RangedSets.RangedSet
open import RangedSetsProp.library
open import RangedSetsProp.RangesProperties

prop_empty : ⦃ o : Ord a ⦄ → ⦃ d : DiscreteOrdered a ⦄ → (v : a) 
           → (not (rSetHas rSetEmpty v)) ≡ true 
prop_empty v = refl

prop_full : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (v : a) → (rSetHas rSetFull v) ≡ true
prop_full v = refl

prop_validNormalised : ⦃ o : Ord a ⦄ → ⦃ d : DiscreteOrdered a ⦄ → (ls : List (Range a)) 
   → (validRangeList (normaliseRangeList ls)) ≡ true
prop_validNormalised ⦃ o ⦄ ⦃ dio ⦄ [] = refl  
prop_validNormalised ⦃ o ⦄ ⦃ dio ⦄ ls@(r1 ∷ rs) = 
  begin 
    (validRangeList (normaliseRangeList ls))
  =⟨⟩  
    (validRangeList (normalise (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) ⦃ sortedList ls ⦄ ⦃ validRangesList ls ⦄))
  =⟨ propIsTrue (validRangeList (normalise (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) ⦃ sortedList ls ⦄ ⦃ validRangesList ls ⦄))
    (normalisedSortedList (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) (sortedList ls) (validRangesList ls)) ⟩ 
    true 
  end

postulate
  prop_empty_rset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → IsTrue (rSetIsEmpty rs) → rSetRanges rs ≡ []
  rangeSetCreation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    → {prf : IsTrue (validRangeList (rSetRanges rs))} → (RS ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs) {prf}) ≡ rs
  rangesEqiv : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → {rs1 rs2 : RSet a} → rSetRanges rs1 ≡ rSetRanges rs2 → rs1 ≡ rs2
  rangesEqiv2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → {rs1 rs2 : List (Range a)} 
    → (prf1 : IsTrue (sortedRangeList rs1)) → (prf2 : IsTrue (validRanges rs1))
    → (prf3 : IsTrue (sortedRangeList rs2)) → (prf4 : IsTrue (validRanges rs2))
    → rs1 ≡ rs2 → normalise rs1 ⦃ prf1 ⦄ ⦃ prf2 ⦄ ≡ normalise rs2 ⦃ prf3 ⦄ ⦃ prf4 ⦄ 

singletonRangeSetHas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) → (v : a) 
  → {prf : IsTrue (validRangeList (r ∷ []))}
  → (rSetHas (RS (r ∷ []) {prf}) v) ≡ rangeHas r v
singletonRangeSetHas r v {prf} = 
  begin 
    (rSetHas (RS (r ∷ []) {prf}) v)
  =⟨⟩  
    ((rangeHas r v) || false)
  =⟨ prop_or_sym (rangeHas r v) false ⟩  
    rangeHas r v 
  end

rSetHasHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → a → (rs : List (Range a)) → {prf : IsTrue (validRangeList rs)} → Bool
rSetHasHelper ⦃  o  ⦄ ⦃ dio ⦄ value rs {prf} = rSetHas ⦃ o ⦄ ⦃ dio ⦄ (RS rs {prf}) value

postulate
  -- the following postulates hold when the boundaries are ordered
  emptyIntersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              → IsFalse (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)

  emptyIntersection2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              → IsFalse (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)           
   
  orderedBoundaries2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            → IsFalse (b2 < b1) 
  -- used for easing the proofs, the true value should be IsTrue (b1 <= b2)                       
  orderedBoundaries3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            → IsTrue (b1 < b2)               
         
{-# TERMINATING #-}
lemma0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    → {prf : IsTrue (validRangeList (rSetRanges rs))}
    → (ranges1 (bounds1 (rSetRanges rs))) ≡ (rSetRanges rs)
lemma0 ⦃ o ⦄ ⦃ dio ⦄ rs@(RS []) {_} = 
    begin
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ []))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ [])
    =⟨⟩
      [] 
    =⟨⟩
      rSetRanges rs      
    end
lemma0 ⦃ o ⦄ ⦃ dio ⦄ rs@(RS (r@(Rg l u) ∷ rgs)) {prf} = 
    begin
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (r ∷ rgs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ ((rangeLower ⦃ o ⦄ ⦃ dio ⦄ r) ∷ ((rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r) ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))))
    =⟨⟩
      ((Rg l u) ∷ ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))    
    =⟨⟩
      (r ∷ ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))
    =⟨ cong (r ∷_) (lemma0 ⦃ o ⦄ ⦃ dio ⦄ (RS rgs {headandtail rs prf}) {headandtail rs prf}) ⟩
      (r ∷ rgs)   
    =⟨⟩
      rSetRanges rs
    end


rangeEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x : Boundary a) → rangeIsEmpty (Rg x x) ≡ true
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll = refl
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ BoundaryAboveAll = refl
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ b@(BoundaryBelow m) =
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 ⦃ o ⦄ refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ b@(BoundaryAbove m) = 
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 ⦃ o ⦄ refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end





merge2Empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) → ⦃ ne : NonEmpty bs ⦄
          → filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 (tail bs ⦃ ne ⦄)) (ranges1 bs)) ≡ []

merge2Empty2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) → ⦃ ne : NonEmpty bs ⦄
          → filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (tail bs ⦃ ne ⦄))) ≡ []  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end    
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end     
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end        
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ []))  (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 [])) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 (ranges1 bounds) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3' ⦃ o ⦄ {((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))}
        {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))}
      (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2  ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ false (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll))
        ∷ (merge2 ((Rg b1 b2) ∷ []) []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2  (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss) )))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 


merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end 
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end  
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end         
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3' ⦃ o ⦄ {((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))}
        {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))}
      (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end           
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
    
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end         


lemma2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) 
               → (filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs)))) ≡ []
lemma2 ⦃ o ⦄ ⦃ dio ⦄ [] =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (setBounds1 []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (BoundaryBelowAll ∷ []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(BoundaryBelowAll ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (BoundaryBelowAll ∷ [])))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  (ranges1 [])))
    =⟨⟩
     (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  []))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(BoundaryAboveAll ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)(merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (setBounds1 (BoundaryAboveAll ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryBelow x) ∷ []) = 
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 ((BoundaryBelow x) ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryAbove x) ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (b ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryAboveAll) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3' ⦃ o ⦄
        {((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))}
          {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))}
        (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelow x) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryAbove x) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end   

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b ∷ bs2@(c ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) (ranges1 (b ∷ bs2)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) ((Rg b c) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (if_then_else_ (b < c) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))) (merge2 (ranges1 bs) (ranges1 bss)))) 
    
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg b c)) ∷_) (propIf2 (b < c) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b c))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false)  
       ((rangeIntersection (Rg a b) (Rg b c)) ∷
         (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2)))))  
         (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b c) ⟩   
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b ∷ bs2) ⟩ 
      []                    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAboveAll) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)(merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []      
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelowAll) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3' ⦃ o ⦄
      {((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))}
      {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []) }
      (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAbove x) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelow x) ∷ []) =
          (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end   


merge2' : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → List (Range a) → List (Range a)
merge2' ms1 ms2 = merge2 ms2 ms1


prop_empty_intersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsEmpty (rSetIntersection rs (rSetNegation rs)) ≡ true
prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges) {prf} =
    begin
      rSetIsEmpty (rSetIntersection rs (rSetNegation rs))
    =⟨⟩
      rSetIsEmpty (rSetIntersection rs 
       (RS (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))) {negation rs prf}))
    
    =⟨⟩    
      rSetIsEmpty (RS (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) 
        (merge2 ranges (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))))) 
              {intersection0 rs (RS (ranges1 (setBounds1 (bounds1 ranges))) {negation rs prf})}) 
    =⟨⟩ 
      rangesAreEmpty (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ranges (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))))) 
    =⟨ cong rangesAreEmpty (cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) 
              (cong (merge2' (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)))) (sym (lemma0 rs {prf})))) ⟩  
      rangesAreEmpty (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)) 
          (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)))))             
    =⟨ cong rangesAreEmpty (lemma2 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)) ⟩ 
     rangesAreEmpty ⦃ o ⦄ ⦃ dio ⦄ []  
    =⟨⟩           
      true
   end  

prop_empty_intersection_istrue : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → IsTrue (rSetIsEmpty (rSetIntersection rs (rSetNegation rs))) 
prop_empty_intersection_istrue ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges) {prf} = subst IsTrue (sym (prop_empty_intersection rs {prf})) IsTrue.itsTrue

prop_empty_intersection_ranges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → rSetRanges (rSetIntersection rs (rSetNegation rs)) ≡ [] 
prop_empty_intersection_ranges ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges {prf}) = prop_empty_rset (rSetIntersection rs (rSetNegation rs)) (prop_empty_intersection_istrue rs {prf})

prop_empty_intersection_does_not_contain_anything : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → (v : a) → (rSetIntersection rs (rSetNegation rs)) -?- v ≡ false 
prop_empty_intersection_does_not_contain_anything {{ o }} {{ dio }} rs@(RS ranges {prf}) v = 
  begin 
    (rSetIntersection rs (rSetNegation rs)) -?- v 
   =⟨⟩
    rangeListHas (rSetRanges (rSetIntersection rs (rSetNegation rs))) v  
    =⟨⟩
    rangeListHas1 v (rSetRanges (rSetIntersection rs (rSetNegation rs))) 
   =⟨ cong (rangeListHas1 v) (prop_empty_intersection_ranges rs) ⟩
    rangeListHas [] v
   =⟨⟩
   false 
  end   

prop_empty_intersection_does_not_contain_anything_isFalse : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → (v : a) → IsFalse ((rSetIntersection rs (rSetNegation rs)) -?- v)
prop_empty_intersection_does_not_contain_anything_isFalse {{o}} {{dio}} rs v = subst IsFalse (sym (prop_empty_intersection_does_not_contain_anything rs v)) IsFalse.itsFalse



prop_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubset rs rs ≡ true
prop_subset ⦃ o ⦄ ⦃ dio ⦄ rs {prf} = 
   begin
    rSetIsSubset rs rs
   =⟨⟩
    rSetIsEmpty (rSetDifference rs rs)
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs (rSetNegation rs))
   =⟨ prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf} ⟩
     true   
   end 

prop_strictSubset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubsetStrict rs rs ≡ false
prop_strictSubset ⦃ o ⦄ ⦃ dio ⦄ rs {prf} = 
   begin
    rSetIsSubsetStrict rs rs
   =⟨⟩
    rSetIsEmpty (rSetDifference rs rs) && (not (rSetIsEmpty (rSetDifference rs rs)))
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs (rSetNegation rs)) 
      && (not (rSetIsEmpty (rSetDifference rs rs)))
   =⟨ cong (_&& (not (rSetIsEmpty (rSetDifference rs rs)))) (prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf}) ⟩
    true && (not (rSetIsEmpty (rSetIntersection rs (rSetNegation rs))))
   =⟨⟩
    (not (rSetIsEmpty (rSetIntersection rs (rSetNegation rs))))
   =⟨ cong not (prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf}) ⟩  
     not true 
   =⟨⟩    
     false   
   end 


unionHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → validRangeList (rSetRanges (rSetUnion rs1 rs2)) 
         ≡ validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 ⦄)
unionHelper ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1) rs2@(RS ls2) prf1 prf2 =   
  begin 
     validRangeList (rSetRanges (rSetUnion rs1 rs2)) 
  =⟨⟩ 
     validRangeList (rSetRanges (RS (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 ⦄) {unionHolds rs1 rs2}))
  =⟨⟩
     validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 ⦄)
  end

union2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → IsTrue (validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 ⦄))
         → IsTrue (validRangeList (rSetRanges (rSetUnion rs1 rs2) ))
union2 rs1 rs2 prf1 prf2 prf = subst IsTrue (sym (unionHelper rs1 rs2 prf1 prf2)) prf

{-# TERMINATING #-}
prop_rsethas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) 
                        → (v : a) → (rSetHas rs1 v) ≡ (rangeListHas (rSetRanges rs1) v)
prop_rsethas ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges) v = refl               


postulate 
  rsetHasNormalised : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (v : a) 
                    → (prf1 : IsTrue (sortedRangeList rs1)) → (prf2 : IsTrue (validRanges rs1)) 
                    → rangeListHas (normalise rs1 ⦃ prf1 ⦄ ⦃ prf2 ⦄) v ≡ rangeListHas rs1 v
  rsetHasFiltered : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (v : a) 
                    → rangeListHas ((filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) rs1) v ≡ rangeListHas rs1 v                  

prop_merge1has : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
  → (v : a) → rangeListHas (merge1 ls1 ls2) v ≡ ((rangeListHas ls1 v) || (rangeListHas ls2 v))

prop_merge1hasHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
  → {{ ne1 : NonEmpty ls1 }} → {{ ne2 : NonEmpty ls2 }}
  → (v : a) → (b : Bool) → rangeListHas (if_then_else_ b ((head ls1) ∷ (merge1 (tail ls1) ls2)) ((head ls2) ∷ (merge1 ls1 (tail ls2)))) v ≡ ((rangeListHas ls1 v) || (rangeListHas ls2 v))
prop_merge1hasHelper ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v true = 
   begin
    rangeListHas (h1 ∷ (merge1 t1 ls2)) v
   =⟨⟩
    ((rangeHas h1 v) || (rangeListHas (merge1 t1 ls2) v))
   =⟨ cong ((rangeHas h1 v) ||_) (prop_merge1has t1 ls2 v) ⟩
    ((rangeHas h1 v) || ((rangeListHas t1 v) || (rangeListHas ls2 v)))
   =⟨ sym (prop_or_assoc (rangeHas h1 v) (rangeListHas t1 v) (rangeListHas ls2 v)) ⟩
    (((rangeHas h1 v) || (rangeListHas t1 v)) || (rangeListHas ls2 v))   
   =⟨⟩         
    ((rangeListHas ls1 v) || (rangeListHas ls2 v)) 
   end 
prop_merge1hasHelper ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v false = 
   begin
    rangeListHas (h2 ∷ (merge1 ls1 t2)) v
   =⟨⟩
    ((rangeHas h2 v) || (rangeListHas (merge1 ls1 t2) v))
   =⟨ cong ((rangeHas h2 v) ||_) (prop_merge1has ls1 t2 v) ⟩
    ((rangeHas h2 v) || ((rangeListHas ls1 v) || (rangeListHas t2 v)))
   =⟨ prop_or_sym (rangeHas h2 v) ((rangeListHas ls1 v) || (rangeListHas t2 v)) ⟩
    (((rangeListHas ls1 v) || (rangeListHas t2 v)) || (rangeHas h2 v) )   
   =⟨ prop_or_assoc (rangeListHas ls1 v) (rangeListHas t2 v) (rangeHas h2 v) ⟩        
    ((rangeListHas ls1 v) || ((rangeListHas t2 v) || (rangeHas h2 v)))   
   =⟨ cong ((rangeListHas ls1 v) ||_) (prop_or_sym (rangeListHas t2 v) (rangeHas h2 v)) ⟩       
    ((rangeListHas ls1 v) || (rangeListHas ls2 v)) 
   end 

prop_merge1has ⦃ o ⦄ ⦃ dio ⦄ [] [] v = refl 
prop_merge1has ⦃ o ⦄ ⦃ dio ⦄ (r1 ∷ t1) [] v = 
   begin
    rangeListHas (r1 ∷ t1) v
   =⟨ sym (prop_or_false2 (rangeListHas (r1 ∷ t1) v)) ⟩
    ((rangeListHas (r1 ∷ t1) v) || (rangeListHas [] v)) 
   end  
prop_merge1has ⦃ o ⦄ ⦃ dio ⦄ [] (r2 ∷ t2) v = 
   begin
    rangeListHas (r2 ∷ t2) v
   =⟨⟩
   (false || (rangeListHas (r2 ∷ t2) v)) 
   =⟨⟩
    ((rangeListHas [] v) || (rangeListHas (r2 ∷ t2) v)) 
   end  
prop_merge1has ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v =  
   begin
    rangeListHas (if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ls2)) (h2 ∷ (merge1 ls1 t2))) v
   =⟨ prop_merge1hasHelper ls1 ls2 {{NonEmpty.itsNonEmpty}} {{NonEmpty.itsNonEmpty}} v (h1 < h2) ⟩
    ((rangeListHas ls1 v) || (rangeListHas ls2 v)) 
   end 

prop_merge2has : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
  → (v : a) → rangeListHas (merge2 ls1 ls2) v ≡ ((rangeListHas ls1 v) && (rangeListHas ls2 v))


prop_merge2hasHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
  → {{ ne1 : NonEmpty ls1 }} → {{ ne2 : NonEmpty ls2 }}
  → (v : a) → (b : Bool) 
  → rangeListHas ((rangeIntersection (head ls1) (head ls2)) ∷ (if_then_else_ b (merge2 (tail ls1) ls2) (merge2 ls1 (tail ls2)))) v
   ≡ ((rangeListHas ls1 v) && (rangeListHas ls2 v))

prop_merge2has ⦃ o ⦄ ⦃ dio ⦄ [] [] v = refl 
prop_merge2has ⦃ o ⦄ ⦃ dio ⦄ ls1@(r1 ∷ t1) ls2@([]) v = 
   begin
    false
   =⟨⟩
    (false && (rangeListHas ls1 v))
   =⟨ prop_and_sym false (rangeListHas ls1 v) ⟩
    ((rangeListHas ls1 v) && (rangeListHas ls2 v)) 
   end 
prop_merge2has ⦃ o ⦄ ⦃ dio ⦄ ls1@([]) ls2@(r2 ∷ t2) v = 
   begin
    false
   =⟨⟩
    (false && (rangeListHas ls2 v))
   =⟨⟩
    ((rangeListHas ls1 v) && (rangeListHas ls2 v)) 
   end 
prop_merge2has ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v =  
   begin
    rangeListHas ((rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h1 < rangeUpper h2) (merge2 t1 ls2) (merge2 ls1 t2))) v
   =⟨ prop_merge2hasHelper ls1 ls2 {{NonEmpty.itsNonEmpty}} {{NonEmpty.itsNonEmpty}} v (rangeUpper h1 < rangeUpper h2) ⟩
    ((rangeListHas ls1 v) && (rangeListHas ls2 v)) 
   end 

postulate 
  falseinstance1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
    → {{ ne1 : NonEmpty ls1 }} → {{ ne2 : NonEmpty ls2 }} 
    → (v : a) → (b : Bool) → IsFalse b → IsFalse ((rangeListHas (tail ls1) v) && (rangeHas (head ls2) v))
  falseinstance2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
    → {{ ne1 : NonEmpty ls1 }} → {{ ne2 : NonEmpty ls2 }}
    → (v : a) → (b : Bool) → IsTrue b → IsFalse ((rangeHas (head ls1) v) && (rangeListHas (tail ls2) v))  
  assume_ranges_nonempty : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ → (r1 r2 : (Range a)) 
    → IsFalse (rangeIsEmpty r1 || rangeIsEmpty r2)

prop_merge2hasHelper ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v false = 
   begin
    rangeListHas ((rangeIntersection h1 h2) ∷ (merge2 ls1 t2)) v
   =⟨⟩
    ((rangeHas (rangeIntersection h1 h2) v) || (rangeListHas (merge2 ls1 t2) v))
   =⟨ cong ((rangeHas (rangeIntersection h1 h2) v) ||_) (prop_merge2has ls1 t2 v) ⟩
    ((rangeHas (rangeIntersection h1 h2) v) || ((rangeListHas ls1 v) && (rangeListHas t2 v)))
   =⟨ cong (_|| ((rangeListHas ls1 v) && (rangeListHas t2 v))) (sym (prop_IntersectionRange h1 h2 {{assume_ranges_nonempty h1 h2}} v)) ⟩
    (((rangeHas h1 v) && (rangeHas h2 v)) || ((rangeListHas ls1 v) && (rangeListHas t2 v)))    
   =⟨ prop_logic2 (rangeHas h1 v) (rangeListHas t1 v) (rangeHas h2 v) (rangeListHas t2 v) (falseinstance1 ls1 ls2 {{NonEmpty.itsNonEmpty}} {{NonEmpty.itsNonEmpty}} v false IsFalse.itsFalse) ⟩            
    ((rangeListHas ls1 v) && (rangeListHas ls2 v)) 
   end 
prop_merge2hasHelper ⦃ o ⦄ ⦃ dio ⦄ ls1@(h1 ∷ t1) ls2@(h2 ∷ t2) v true = 
   begin
    rangeListHas ((rangeIntersection h1 h2) ∷ (merge2 t1 ls2)) v
   =⟨⟩
    ((rangeHas (rangeIntersection h1 h2) v) || (rangeListHas (merge2 t1 ls2) v))
   =⟨ cong ((rangeHas (rangeIntersection h1 h2) v) ||_) (prop_merge2has t1 ls2 v) ⟩
    ((rangeHas (rangeIntersection h1 h2) v) || ((rangeListHas t1 v) && (rangeListHas ls2 v)))
   =⟨ cong (_|| ((rangeListHas t1 v) && (rangeListHas ls2 v))) (sym (prop_IntersectionRange h1 h2 {{assume_ranges_nonempty h1 h2}} v)) ⟩
    (((rangeHas h1 v) && (rangeHas h2 v)) || ((rangeListHas t1 v) && (rangeListHas ls2 v)))    
   =⟨ prop_logic3 (rangeHas h1 v) (rangeListHas t1 v) (rangeHas h2 v) (rangeListHas t2 v) (falseinstance2 ls1 ls2 {{NonEmpty.itsNonEmpty}} {{NonEmpty.itsNonEmpty}} v true IsTrue.itsTrue) ⟩            
    ((rangeListHas ls1 v) && (rangeListHas ls2 v)) 
   end 


prop_union : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → (v : a) → (rSetHas (rSetUnion rs1 rs2) v) ≡ (rSetHas rs1 v || rSetHas rs2 v)
prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) v = refl            
prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1 {prf1}) rs2@(RS ls2 {prf2}) v = 
   begin
    (rSetHas (RS (normalise (merge1 ls1 ls2) ⦃ merge1Sorted rs1 rs2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 ⦄) {unionHolds rs1 rs2}) v)
   =⟨ prop_rsethas (RS (normalise (merge1 ls1 ls2) ⦃ merge1Sorted rs1 rs2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 ⦄) {unionHolds rs1 rs2}) v ⟩
    rangeListHas (normalise (merge1 ls1 ls2) ⦃ merge1Sorted rs1 rs2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 ⦄) v
   =⟨ rsetHasNormalised (merge1 ls1 ls2) v (merge1Sorted rs1 rs2) (merge1HasValidRanges rs1 rs2) ⟩
     rangeListHas (merge1 ls1 ls2) v
   =⟨ prop_merge1has ls1 ls2 v ⟩
     ((rangeListHas ls1 v) || (rangeListHas ls2 v))
   =⟨ cong ((rangeListHas ls1 v) ||_) (sym (prop_rsethas rs2 v)) ⟩
     ((rangeListHas ls1 v) || (rSetHas rs2 v))  
   =⟨ cong (_|| (rSetHas rs2 v)) (sym (prop_rsethas rs1 v)) ⟩
     ((rSetHas rs1 v) || (rSetHas rs2 v))      
   end   

prop_intersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → (v : a) → (rSetHas (rSetIntersection rs1 rs2) v) ≡ (rSetHas rs1 v && rSetHas rs2 v)
prop_intersection ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) v = refl     
prop_intersection ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS (r1 ∷ r2)) v = refl  
prop_intersection ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS (r1 ∷ r2)) rs2@(RS []) v = 
   begin
    false
   =⟨⟩
    (false && (rSetHas rs1 v))
   =⟨ prop_and_sym false (rSetHas rs1 v) ⟩
     ((rSetHas rs1 v) && false)  
   =⟨⟩
     ((rSetHas rs1 v) && (rSetHas rs2 v))      
   end  
prop_intersection ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1 {prf1}) rs2@(RS ls2 {prf2}) v = 
   begin
    (rSetHas (RS (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ls1 ls2)) {intersection0 rs1 rs2}) v)
   =⟨ prop_rsethas (RS (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ls1 ls2)) {intersection0 rs1 rs2}) v ⟩
    rangeListHas (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ls1 ls2)) v
   =⟨ rsetHasFiltered (merge2 ls1 ls2) v ⟩
     rangeListHas (merge2 ls1 ls2) v
   =⟨ prop_merge2has ls1 ls2 v ⟩
     ((rangeListHas ls1 v) && (rangeListHas ls2 v))
   =⟨ cong ((rangeListHas ls1 v) &&_) (sym (prop_rsethas rs2 v)) ⟩
     ((rangeListHas ls1 v) && (rSetHas rs2 v))  
   =⟨ cong (_&& (rSetHas rs2 v)) (sym (prop_rsethas rs1 v)) ⟩
     ((rSetHas rs1 v) && (rSetHas rs2 v))      
   end  

-- if a value is in a rset, it is not in its negation
prop_negation1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → (v : a) → IsTrue (rs -?- v) -> IsTrue (not (rSetNegation rs -?- v))
prop_negation1 {{ o }} {{ dio }} rs v prf = 
  prop_logic4 (rs -?- v) (rSetNegation rs -?- v) (subst IsFalse (prop_intersection rs (rSetNegation rs) v) (prop_empty_intersection_does_not_contain_anything_isFalse rs v)) prf

-- if a value is in a set's negation, it is not in the set
prop_negation2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → (v : a) → IsFalse (rs -?- v) -> IsFalse (not (rSetNegation rs -?- v))
prop_negation2 {{ o }} {{ dio }} rs v prf = 
  prop_logic5 (rs -?- v) (rSetNegation rs -?- v) (subst IsFalse (prop_intersection rs (rSetNegation rs) v) (prop_empty_intersection_does_not_contain_anything_isFalse rs v)) prf

prop_difference1 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a) 
  → (v : a) -> IsTrue (rs2 -?- v) -> ((rs1 -!- rs2) -?- v) ≡ ((rs1 -?- v) && not (rs2 -?- v))
prop_difference1 {{o}} {{dio}} rs1@(RS ranges1 {prf1}) rs2@(RS ranges2 {prf2}) v prf =
  begin
    ((rs1 -!- rs2) -?- v)
   =⟨⟩
    (rSetIntersection rs1 (rSetNegation rs2)) -?- v    
   =⟨ prop_intersection rs1 (rSetNegation rs2) v ⟩
    ((rs1 -?- v) && ((rSetNegation rs2) -?- v))
   =⟨ cong ((rs1 -?- v) &&_) (not-not ((rSetNegation rs2) -?- v)) ⟩
    ((rs1 -?- v) && (not (not ((rSetNegation rs2) -?- v))))    
   =⟨ cong ((rs1 -?- v) &&_) (cong not (sym (prop_logic0 (rs2 -?- v) ((rSetNegation rs2) -?- v) prf (prop_negation1 rs2 v prf)))) ⟩
    ((rs1 -?- v) && not (rs2 -?- v))    
  end

prop_difference2 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a) 
  → (v : a) -> IsFalse (rs2 -?- v) -> ((rs1 -!- rs2) -?- v) ≡ ((rs1 -?- v) && not (rs2 -?- v))
prop_difference2 {{o}} {{dio}} rs1@(RS ranges1 {prf1}) rs2@(RS ranges2 {prf2}) v prf =
  begin
    ((rs1 -!- rs2) -?- v)
   =⟨⟩
    (rSetIntersection rs1 (rSetNegation rs2)) -?- v    
   =⟨ prop_intersection rs1 (rSetNegation rs2) v ⟩
    ((rs1 -?- v) && ((rSetNegation rs2) -?- v))
   =⟨ cong ((rs1 -?- v) &&_) (not-not ((rSetNegation rs2) -?- v)) ⟩
    ((rs1 -?- v) && (not (not ((rSetNegation rs2) -?- v))))    
   =⟨ cong ((rs1 -?- v) &&_) (cong not (sym (prop_logic0' (rs2 -?- v) ((rSetNegation rs2) -?- v) prf (prop_negation2 rs2 v prf)))) ⟩
    ((rs1 -?- v) && not (rs2 -?- v))    
  end

prop_union_has_sym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
  → (rs1 : RSet a) → (rs2 : RSet a) → (v : a) 
  → ((rs1 -\/- rs2) -?- v) ≡ ((rs2 -\/- rs1) -?- v)
prop_union_has_sym ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1) rs2@(RS ranges2) v = 
  begin 
    ((rs1 -\/- rs2) -?- v) 
  =⟨ (prop_union rs1 rs2 v) ⟩ 
    ((rs1 -?- v) || (rs2 -?- v))
  =⟨ prop_or_sym (rs1 -?- v) (rs2 -?- v) ⟩
    ((rs2 -?- v) || (rs1 -?- v))
  =⟨ sym (prop_union rs2 rs1 v) ⟩
    ((rs2 -\/- rs1) -?- v) 
  end  

prop_union_same_set : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (v : a) → ((rs1 -\/- rs1) -?- v) ≡ (rs1 -?- v)
prop_union_same_set ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1) v = 
  begin 
    ((rs1 -\/- rs1) -?- v) 
  =⟨ (prop_union rs1 rs1 v) ⟩ 
    ((rs1 -?- v) || (rs1 -?- v))
  =⟨ prop_or_same_value (rs1 -?- v) ⟩
    (rs1 -?- v) 
  end  

prop_validNormalisedEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → validRangeList ⦃ o ⦄ ⦃ dio ⦄ (normaliseRangeList ⦃ o ⦄ ⦃ dio ⦄ []) ≡ true
prop_validNormalisedEmpty ⦃ o ⦄ ⦃ dio ⦄ = 
  begin 
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (normaliseRangeList ⦃ o ⦄ ⦃ dio ⦄ []) 
  =⟨⟩ 
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩
    true 
  end  



postulate 
  -- these postulates hold when r1 == r2 does not hold, used for easing the proofs for union/intersection commutes
  equalityRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r1 : Range a) → (r2 : Range a)
                  → (r1 < r2) ≡ (not (r2 < r1))                               
  equalityRanges2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r1 : Range a) → (r2 : Range a)
                  → (rangeUpper r1 < rangeUpper r2) ≡ (not (rangeUpper r2 < rangeUpper r1))

prop_sym_merge1' :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
  → ⦃ ne1 : NonEmpty rs1 ⦄ → ⦃ ne2 : NonEmpty rs2 ⦄ → (b : Bool)
  → if_then_else_ b ((head rs1 ⦃ ne1 ⦄) ∷ (merge1 (tail rs1 ⦃ ne1 ⦄) rs2)) ((head rs2 ⦃ ne2 ⦄) ∷ (merge1 rs1 (tail rs2 ⦃ ne2 ⦄))) ≡
      if_then_else_ (not b) ((head rs2 ⦃ ne2 ⦄) ∷ (merge1 (tail rs2 ⦃ ne2 ⦄) rs1)) ((head rs1 ⦃ ne1 ⦄) ∷ (merge1 rs2 (tail rs1 ⦃ ne1 ⦄)))

prop_sym_merge1 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
                  → merge1 rs1 rs2 ≡ merge1 rs2 rs1 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ [] [] = refl 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) [] = refl                 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ [] ms2@(h2 ∷ t2) = refl 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
  begin 
    merge1 ms1 ms2 
   =⟨⟩
    if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2)) 
   =⟨ prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1 ms2 (h1 < h2) ⟩
    if_then_else_ (not (h1 < h2)) (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1)) 
   =⟨ cong (ifThenElseHelper (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))) (sym (equalityRanges h2 h1)) ⟩    
    if_then_else_ (h2 < h1) (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1)) 
   =⟨⟩
    merge1 ms2 ms1
  end  


prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) true = 
  begin 
    if_then_else_ true (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
   =⟨⟩
    (h1 ∷ (merge1 t1 ms2)) 
   =⟨ cong (h1 ∷_) (prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ t1 ms2) ⟩
    (h1 ∷ (merge1 ms2 t1))   
   =⟨⟩  
    if_then_else_ false (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))  
  end  
prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) false = 
  begin 
    if_then_else_ false (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
   =⟨⟩
    (h2 ∷ (merge1 ms1 t2)) 
   =⟨ cong (h2 ∷_) (prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1 t2) ⟩
    (h2 ∷ (merge1 t2 ms1))   
   =⟨⟩  
    if_then_else_ true (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))  
  end 

prop_sym_sortedRangeList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
                          → (sortedRangeList (merge1 ls1 ls2)) ≡ (sortedRangeList (merge1 ls2 ls1))
prop_sym_sortedRangeList ⦃  o  ⦄ ⦃  dio  ⦄ ls1 ls2 =  (cong sortedRangeList (prop_sym_merge1 ls1 ls2))

prop_sym_validRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
                          →  (validRanges (merge1 ls1 ls2)) ≡  (validRanges (merge1 ls2 ls1))
prop_sym_validRanges ⦃  o  ⦄ ⦃  dio  ⦄ ls1 ls2 =  (cong validRanges (prop_sym_merge1 ls1 ls2))

prop_union_commutes : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
                      → (rSetUnion rs1 rs2) ≡ (rSetUnion rs2 rs1)
prop_union_commutes (RS []) (RS []) = refl
prop_union_commutes (RS ranges@(r ∷ rs)) (RS []) = refl
prop_union_commutes (RS []) (RS ranges@(r ∷ rs)) = refl
prop_union_commutes ⦃ o ⦄ ⦃ dio ⦄ RS1@(RS ls1@(r1 ∷ rs1) {prf1} ) RS2@(RS ls2@(r2 ∷ rs2) {prf2})=
  begin 
    (rSetUnion RS1 RS2) 
   =⟨⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ (normalise ⦃ o ⦄ ⦃ dio ⦄ (merge1 ⦃ o ⦄ ⦃ dio ⦄ ls1 ls2) ⦃ merge1Sorted RS1 RS2 ⦄ 
    ⦃ merge1HasValidRanges RS1 RS2 ⦄) {unionHolds RS1 RS2}
   =⟨ rangesEqiv (rangesEqiv2 (merge1Sorted RS1 RS2) (merge1HasValidRanges RS1 RS2)
     (merge1Sorted RS2 RS1) (merge1HasValidRanges RS2 RS1) (prop_sym_merge1 ls1 ls2))  ⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ (normalise ⦃ o ⦄ ⦃ dio ⦄ (merge1 ⦃ o ⦄ ⦃ dio ⦄ ls2 ls1) ⦃ merge1Sorted RS2 RS1 ⦄ 
    ⦃ merge1HasValidRanges RS2 RS1 ⦄) {unionHolds RS2 RS1}
  =⟨⟩
   (rSetUnion RS2 RS1)
     end

prop_sym_merge2 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
                  → merge2 rs1 rs2 ≡ merge2 rs2 rs1 

prop_sym_merge2' :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
  → ⦃ ne1 : NonEmpty rs1 ⦄ → ⦃ ne2 : NonEmpty rs2 ⦄ → (b : Bool)
  → (if_then_else_ b (merge2 (tail rs1 ⦃ ne1 ⦄) rs2) (merge2 rs1 (tail rs2 ⦃ ne2 ⦄))) ≡
      (if_then_else_ (not b) (merge2 (tail rs2 ⦃ ne2 ⦄) rs1) (merge2 rs2 (tail rs1 ⦃ ne1 ⦄)))
prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) true = 
  begin 
    (if_then_else_ true (merge2 t1 ms2) (merge2 ms1 t2)) 
  =⟨⟩  
   (merge2 t1 ms2)
  =⟨ prop_sym_merge2 t1 ms2 ⟩
   (merge2 ms2 t1)
  =⟨⟩
   if_then_else_ false (merge2 t2 ms1) (merge2 ms2 t1)
  end  
prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) false = 
  begin 
    (if_then_else_ false (merge2 t1 ms2) (merge2 ms1 t2)) 
  =⟨⟩  
   (merge2 ms1 t2)
  =⟨ prop_sym_merge2 ms1 t2 ⟩
   (merge2 t2 ms1)
  =⟨⟩
   if_then_else_ true (merge2 t2 ms1) (merge2 ms2 t1)
     end  

prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ [] [] = refl 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) [] = refl                 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ [] ms2@(h2 ∷ t2) = refl 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
  begin 
    merge2 ms1 ms2 
   =⟨⟩
    (rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h1 < rangeUpper h2) (merge2 t1 ms2) (merge2 ms1 t2)) 
   =⟨ cong ((rangeIntersection h1 h2) ∷_) (prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1 ms2 (rangeUpper h1 < rangeUpper h2)) ⟩
    (rangeIntersection h1 h2) ∷ (if_then_else_ (not (rangeUpper h1 < rangeUpper h2)) (merge2 t2 ms1) (merge2 ms2 t1))  
   =⟨ cong ((rangeIntersection h1 h2) ∷_) (cong (ifThenElseHelper (merge2 t2 ms1) (merge2 ms2 t1)) (sym (equalityRanges2 h2 h1))) ⟩    
    ((rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) 
   =⟨ cong (_∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) (prop_intersection_sym h1 h2) ⟩    
    ((rangeIntersection h2 h1) ∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) 
   =⟨⟩
    merge2 ms2 ms1
  end 

prop_intersection_commutes : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                      → {prf1 : IsTrue (validRangeList (rSetRanges rs1))} → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
                      → (rSetIntersection rs1 rs2) ≡ (rSetIntersection rs2 rs1)
prop_intersection_commutes (RS []) (RS []) = refl
prop_intersection_commutes (RS ranges@(r ∷ rs)) (RS []) = refl
prop_intersection_commutes (RS []) (RS ranges@(r ∷ rs)) = refl
prop_intersection_commutes ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1@(r1 ∷ rss1)) rs2@(RS ls2@(r2 ∷ rss2)) {prf1} {prf2} =
  begin 
    (rSetIntersection rs1 rs2) 
   =⟨⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ 
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ls1 ls2)) 
         {intersection0 rs1 rs2}
   =⟨ rangesEqiv (cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (prop_sym_merge2 ls1 ls2)) ⟩
     RS ⦃ o ⦄ ⦃ dio ⦄ 
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ls2 ls1)) 
         {intersection0 rs2 rs1}
  =⟨⟩
   (rSetIntersection rs2 rs1)
     end

-- if x is strict subset of y, y is not strict subset of x 
-- prop_subset_not1 asserts that rSetIsSubstrict x y is true 
-- this means that rSetIsEmpty (rSetDifference x y) is true 
-- and rSetEmpty (rSetDifference x y) is false
prop_subset_not1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  -> (a1 : IsTrue (rSetIsEmpty (rSetDifference rs1 rs2))) 
  -> (a2 : IsTrue (not (rSetIsEmpty (rSetDifference rs2 rs1))))
  → (rSetIsSubsetStrict rs1 rs2) ≡ (not (rSetIsSubsetStrict rs2 rs1)) 
prop_subset_not1 {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} a1 a2 = 
  begin 
    rSetIsSubsetStrict rs1 rs2
  =⟨⟩
   (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1)))
  =⟨ not-not (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1))) ⟩  
    not (not (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1))))
  =⟨ cong not (prop_demorgan (rSetIsEmpty (rSetDifference rs1 rs2)) (not (rSetIsEmpty (rSetDifference rs2 rs1)))) ⟩
    not ((not (rSetIsEmpty (rSetDifference rs1 rs2))) || (not (not (rSetIsEmpty (rSetDifference rs2 rs1)))))
  =⟨ cong not (cong ((not (rSetIsEmpty (rSetDifference rs1 rs2))) ||_) (sym (not-not (rSetIsEmpty (rSetDifference rs2 rs1))))) ⟩  
    not ((not (rSetIsEmpty (rSetDifference rs1 rs2))) || (rSetIsEmpty (rSetDifference rs2 rs1)))
  =⟨ cong not (prop_or_sym (not (rSetIsEmpty (rSetDifference rs1 rs2))) (rSetIsEmpty (rSetDifference rs2 rs1))) ⟩    
    not (rSetIsEmpty (rSetDifference rs2 rs1) || not (rSetIsEmpty (rSetDifference rs1 rs2)))
  =⟨ cong not (prop_or_and_eqiv_false (rSetIsEmpty (rSetDifference rs2 rs1)) 
    (not (rSetIsEmpty (rSetDifference rs1 rs2)))
    (isTrueAndIsFalse2 a2)
    (isTrueAndIsFalse1 a1)) ⟩
   not (rSetIsEmpty (rSetDifference rs2 rs1) && not (rSetIsEmpty (rSetDifference rs1 rs2)))
  =⟨⟩
   not (rSetIsSubsetStrict rs2 rs1)
 end

-- if x is strict subset of y, y is not strict subset of x 
-- prop_subset_not2 asserts that rSetIsSubstrict x y is false 
-- this means that rSetIsEmpty (rSetDifference x y) is false 
-- and rSetEmpty (rSetDifference x y) is true
prop_subset_not2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  -> (a1 : IsFalse (rSetIsEmpty (rSetDifference rs1 rs2))) 
  -> (a2 : IsFalse (not (rSetIsEmpty (rSetDifference rs2 rs1))))
  → (rSetIsSubsetStrict rs1 rs2) ≡ (not (rSetIsSubsetStrict rs2 rs1)) 
prop_subset_not2 {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} a1 a2 = 
  begin 
    rSetIsSubsetStrict rs1 rs2
  =⟨⟩
   (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1)))
  =⟨ not-not (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1))) ⟩  
    not (not (rSetIsEmpty (rSetDifference rs1 rs2) && not (rSetIsEmpty (rSetDifference rs2 rs1))))
  =⟨ cong not (prop_demorgan (rSetIsEmpty (rSetDifference rs1 rs2)) (not (rSetIsEmpty (rSetDifference rs2 rs1)))) ⟩
    not ((not (rSetIsEmpty (rSetDifference rs1 rs2))) || (not (not (rSetIsEmpty (rSetDifference rs2 rs1)))))
  =⟨ cong not (cong ((not (rSetIsEmpty (rSetDifference rs1 rs2))) ||_) (sym (not-not (rSetIsEmpty (rSetDifference rs2 rs1))))) ⟩  
    not ((not (rSetIsEmpty (rSetDifference rs1 rs2))) || (rSetIsEmpty (rSetDifference rs2 rs1)))
  =⟨ cong not (prop_or_sym (not (rSetIsEmpty (rSetDifference rs1 rs2))) (rSetIsEmpty (rSetDifference rs2 rs1))) ⟩    
    not (rSetIsEmpty (rSetDifference rs2 rs1) || not (rSetIsEmpty (rSetDifference rs1 rs2)))
  =⟨ cong not (prop_or_and_eqiv_true (rSetIsEmpty (rSetDifference rs2 rs1)) 
    (not (rSetIsEmpty (rSetDifference rs1 rs2)))
    (isTrueAndIsFalse3 a2)
    (isTrueAndIsFalse4 a1)) ⟩
   not (rSetIsEmpty (rSetDifference rs2 rs1) && not (rSetIsEmpty (rSetDifference rs1 rs2)))
  =⟨⟩
   not (rSetIsSubsetStrict rs2 rs1)
 end 

prop_strictSubset_means_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  → IsTrue (rSetIsSubsetStrict rs1 rs2) -> IsTrue (rSetIsSubset rs1 rs2)
prop_strictSubset_means_subset {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} prf = isTrue&&₁ {(rSetIsSubset rs1 rs2)} prf

