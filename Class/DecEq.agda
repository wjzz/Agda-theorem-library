{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Class.DecEq where

open import Data.Bool using (Bool; true; false)

import Data.Bool 
import Data.Nat
import Data.Unit 
import Data.Fin
import Data.Fin.Props

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------
-- The decidable equality type class

record DecEq (A : Set) : Set where
  constructor mkDecEq
  field 
    _≟_ : Decidable {A = A} _≡_

open DecEq {{...}} public

--------------------------------------------------
-- instances 

boolDecEq : DecEq Data.Bool.Bool
boolDecEq = mkDecEq Data.Bool._≟_

unitDecEq : DecEq Data.Unit.⊤
unitDecEq = mkDecEq Data.Unit._≟_

natDecEq : DecEq Data.Nat.ℕ
natDecEq = mkDecEq Data.Nat._≟_

finDecEq : ∀ {n} → DecEq (Data.Fin.Fin n)
finDecEq = mkDecEq Data.Fin.Props._≟_

--------------------------------------------------
-- using the definitions

private
  test1 : Bool
  test1 with 1 ≟ 2
  test1 | yes p = true
  test1 | no ¬p = false

  test2 : Bool
  test2 with true ≟ false
  test2 | yes p = true
  test2 | no ¬p = false
  