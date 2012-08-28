{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Data.HetVec where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Product

open import Data.Vec.Utils 

import Level

-----------------------------
--  Heterogeneous vectors  --
-----------------------------

data HetVec {l} : ∀ {n : ℕ} → Vec (Set l) n → Set (Level.suc l) where
  []  : HetVec []
  _∷_ : ∀ {n t} {v : Vec (Set l) n} 
      → (x : t) 
      → (h : HetVec v) 
      → HetVec (t ∷ v)

------------------------
--  Basic operations  --
------------------------

-- het. vec lookup:

_!!_ : ∀ {l}{n : ℕ} {v : Vec (Set l) n} → HetVec v → (i : Fin n) → lookup i v

[]      !! ()
(x ∷ h) !! zero  = x
(x ∷ h) !! suc i = h !! i


hlookup : {A : Set}{n : ℕ} 
        → (v : Vec A n) 
        → (f : A → Set)
        → HetVec (Data.Vec.map f v)
        → (i : Fin n) 
        → f (lookup i v)

hlookup [] _ _ ()
hlookup (x ∷ v) f (x₁ ∷ Δ) zero = x₁
hlookup (_ ∷ v) f (_  ∷ Δ) (suc i) = hlookup v f Δ i

--------------------
--  Permutations  --
--------------------

infix 3 _==_

data _==_ {l} : ∀{n}{v1 v2 : Vec (Set l) n} → HetVec v1 → HetVec v2 → Set (Level.suc l) where

  nil : [] == []

  swp : ∀ {n}{A B : Set l}{a : A}{b : B}
      → {Γ : Vec (Set l) n}
      → {Δ : HetVec Γ}
      → a ∷ b ∷ Δ == b ∷ a ∷ Δ

  cns : ∀ {n}{A : Set l}{a : A}
      → {Γ Γ' : Vec (Set l) n}
      → {Δ  : HetVec Γ}
      → {Δ' : HetVec Γ'}
      →     Δ == Δ'
      → a ∷ Δ == a ∷ Δ'

  trn : ∀ {n}
      → {Γ1 Γ2 Γ3 : Vec (Set l) n}
      → {Δ1  : HetVec Γ1}
      → {Δ2  : HetVec Γ2}
      → {Δ3  : HetVec Γ3}
      → Δ1 == Δ2
      → Δ2 == Δ3
      → Δ1 == Δ3


-- type vectors must be permutations themselves:

perm-underlying : ∀ {l}{n}
                → {v1 v2 : Vec (Set l) n} 
                → {Δ1 : HetVec v1}
                → {Δ2 : HetVec v2}
                → Δ1 == Δ2
                → v1 ≈ v2

perm-underlying nil = nil
perm-underlying swp = swp
perm-underlying (cns perm)       = cns (perm-underlying perm)
perm-underlying (trn perm perm₁) = trn (perm-underlying perm) (perm-underlying perm₁)

-- permutation reading

perm-read : {A : Set}
          → {n : ℕ}
          → (f : A → Set)
          → {Γ Γ' : Vec A n}
          → Γ ≈ Γ'
          → (Δ : HetVec (Data.Vec.map f Γ))
          → Σ[ Δ' ∶ HetVec (Data.Vec.map f Γ') ](Δ == Δ')

perm-read f nil [] = [] , nil
perm-read f swp (fb ∷ fa ∷ Δ) = (fa ∷ fb ∷ Δ) , swp
perm-read f (cns perm) (fa ∷ Δ) with perm-read f perm Δ
... | Δ' , prf = fa ∷ Δ' , cns prf
perm-read f (trn perm perm₁) Δ with perm-read f perm Δ
... | Δ' , prf with perm-read f perm₁ Δ'
... | Δ'' , prf2 = Δ'' , trn prf prf2
