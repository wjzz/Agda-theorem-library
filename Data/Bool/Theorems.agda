module Data.Bool.Theorems where

open import Data.Bool
open import Relation.Binary.PropositionalEquality

lem-∧-inv1 : {b1 b2 : Bool} → b1 ∧ b2 ≡ true → b1 ≡ true
lem-∧-inv1 {true}  p = refl
lem-∧-inv1 {false} p = p

lem-∧-inv2 : {b1 b2 : Bool} → b1 ∧ b2 ≡ true → b2 ≡ true
lem-∧-inv2 {true}          p = p
lem-∧-inv2 {false} {true}  p = refl
lem-∧-inv2 {false} {false} p = p

lem-not-inv : (b : Bool) → not (not b) ≡ b
lem-not-inv true  = refl
lem-not-inv false = refl
