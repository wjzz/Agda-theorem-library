module Data.Nat.Compare where

open import Data.Nat hiding (compare)

{- 
   My own comparing function and result datatype. 
   The compare function from Data.Nat produces a lot of noise.
-}
  
data Ord : Set where
 LT EQ GT : Ord

compare : ℕ → ℕ → Ord
compare zero zero    = EQ
compare zero (suc n) = LT
compare (suc n) zero = GT
compare (suc n) (suc n') = compare n n'
