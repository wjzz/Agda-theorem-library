module Data.Vec.Theorems where

open import Data.Nat
open import Data.Nat.Theorems
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{- ++ properties -}

lem-append-l-nil : ∀ {A : Set} {n} → (v : Vec A n) → v ≡ subst (Vec A) (lem-plus-n-0 n) (v ++ [])
lem-append-l-nil [] = refl
lem-append-l-nil (x ∷ xs) with lem-append-l-nil xs
... | rec = trans (cong (λ l → x ∷ l) rec) {!!} -- subst v (cong suc t[n] l) ==? subst v t[suc n] l ?

{- Reverse and ++ relationship -}

lem-rev-++ : ∀ {A : Set} {n m} → (v1 : Vec A n) → (v2 : Vec A m) → reverse (v1 ++ v2) ≡ (subst (Vec A) (lem-plus-comm m n) (reverse v2 ++ reverse v1))
lem-rev-++ v1 v2 = {!!}