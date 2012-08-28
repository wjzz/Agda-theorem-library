{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Data.Vec.Utils where

open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Product hiding (map)
open import Data.Vec
open import Data.Sum hiding (map)
open import Data.Maybe

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Empty

----------------------
--  Non-membership  --
----------------------

infix 4 _∉_ 

_∉_ : {A : Set} {n : ℕ} → A → Vec A n → Set
a ∉ v = ¬ (a ∈ v)

-------------------------
--  Membership lemmas  --
-------------------------

member-here-or-there : ∀ {a}{A : Set a}
                     → {n : ℕ}
                     → Decidable (_≡_ {A = A})
                     → {a b : A}
                     → {v : Vec A n}
                     → a ∈ (b ∷ v)
                     → a ≡ b ⊎ a ∈ v

member-here-or-there decEq here = inj₁ refl
member-here-or-there decEq (there inn) = inj₂ inn

-------------------------------
--  Membership is decidable  --
-------------------------------

member? : ∀ {a}{A : Set a}
        → {n : ℕ}
        → Decidable (_≡_ {A = A})
        → (a : A)
        → (v : Vec A n)
        → Dec (a ∈ v)

member? decEq a [] = no (λ ())
member? decEq a (b ∷ bs)  with decEq a b
member? decEq a (.a ∷ bs) | yes refl = yes here
... | no ¬eq with member? decEq a bs
... | yes later = yes (there later)
... | no not-in = no (λ inn → [ ¬eq , not-in ]′ (member-here-or-there decEq inn))


findKey : ∀ {A B : Set}
        → {n : ℕ}
        → Decidable (_≡_ {A = A})
        → A
        → Vec (A × B) n
        → Maybe B

findKey decEq a [] = nothing
findKey decEq a ((x , y) ∷ xs) with decEq a x
... | yes _ = just y
... | no _  = findKey decEq a xs


-------------------------------------------------------------------------------
--  Returns the element at the given index along with a proof of membership  --
-------------------------------------------------------------------------------

_!_ : {A : Set} {n : ℕ} → (v : Vec A n) → Fin n → Σ[ a ∶ A ] (a ∈ v)
[] ! ()
(x ∷ xs) ! zero  = x , here
(x ∷ xs) ! suc i with xs ! i
(x ∷ xs) ! suc i | a , p = a , there p

--------------------------------------------------------------
--  Applies a given function to all elements of a vector.   
--                                                          
--  At each call a proof of membership in the original vector 
--  is given.                                                
--------------------------------------------------------------

-- note: the order of v and f can't be reversed because f depends on v

map-in : {A B : Set} {n : ℕ} → (v : Vec A n) → (f : (a : A) → (a ∈ v) → B) → Vec B n
map-in []       f = []
map-in (x ∷ xs) f = f x here ∷ map-in xs (λ a a∈xs → f a (there a∈xs))

---------------------------------------------------------------
--  Concats a vector of vectors.                       
--
--  This is a more general version of concat found in std-lib's
--  Data.Vec, because it allows each vector to be of different
--  length.
---------------------------------------------------------------

jaggedConcat : {A : Set} {n : ℕ} → Vec (∃ (Vec A)) n → ∃ (Vec A)
jaggedConcat [] = 0 , []
jaggedConcat ((n , v) ∷ xs) with jaggedConcat xs
... | (n' , vs) = (n + n') , (v ++ vs)


-- basically does the same thing as jaggedConcat, but has a more precise type

jaggedConcat' : {A : Set} {n : ℕ} → (v : Vec (∃ (Vec A)) n) → Vec A (sum (map proj₁ v))
jaggedConcat' []             = []
jaggedConcat' ((n , v) ∷ xs) = v ++ jaggedConcat' xs

----------------------------------------------------------
--  Distinctness of vector elements.
--
--  A vector is distinct if every element of it is unique
---------------------------------------------------------

data distinct-v {A : Set} : {n : ℕ} → Vec A n → Set where
  dist-nil  : distinct-v []
  dist-cons : {n : ℕ} {a : A} {v : Vec A n} → (dist : distinct-v v) → a ∉ v → distinct-v (a ∷ v)

---------------------------------------------------
--  The subvector relation (order is important)  --
---------------------------------------------------

data _⊂_ {A : Set} : {n1 n2 : ℕ} → Vec A n1 → Vec A n2 → Set where
  nil : {n : ℕ} → (v : Vec A n) → [] ⊂ v
  here  : {n1 n2 : ℕ} → {v1 : Vec A n1} → {v2 : Vec A n2} → (a : A) → v1 ⊂ v2 → (a ∷ v1) ⊂ (a ∷ v2)
  there : {n1 n2 : ℕ} → {v1 : Vec A n1} → {v2 : Vec A n2} → (a : A) → v1 ⊂ v2 → v1 ⊂ (a ∷ v2)

lem-⊂-refl : {A : Set}{n : ℕ} → (v : Vec A n) → v ⊂ v
lem-⊂-refl [] = nil []
lem-⊂-refl (x ∷ xs) = here x (lem-⊂-refl xs)

lem-⊂-extend : {A : Set}{n1 n2 : ℕ} → (v1 : Vec A n1) → (v2 : Vec A n2) → v1 ⊂ v2 → (a : A) → a ∈ v1 → a ∈ v2
lem-⊂-extend .[] v2 (nil .v2) a ()
lem-⊂-extend .(a ∷ v1) .(a ∷ v2) (here {n1} {n2} {v1} {v2} a y) .a here = here
lem-⊂-extend .(a ∷ v1) .(a ∷ v2) (here {n1} {n2} {v1} {v2} a y) a' (there x∈xs) = there (lem-⊂-extend v1 v2 y a' x∈xs)
lem-⊂-extend v1 .(a ∷ v2) (there {n1} {n2} {.v1} {v2} a y) a' av1 = there (lem-⊂-extend v1 v2 y a' av1)

lem-⊂-distinct : {A : Set}{n1 n2 : ℕ} → (v1 : Vec A n1) → (v2 : Vec A n2) → distinct-v v2 → v1 ⊂ v2 → distinct-v v1
lem-⊂-distinct .[] v2 dist-v2 (nil .v2) = dist-nil
lem-⊂-distinct .(a ∷ v1) .(a ∷ v2) (dist-cons dist y) (here {n1} {n2} {v1} {v2} a y') = 
  dist-cons (lem-⊂-distinct v1 v2 dist y') 
  (λ x → y (lem-⊂-extend v1 v2 y' a x))
lem-⊂-distinct v1 .(a ∷ v2) (dist-cons dist y) (there {n1} {n2} {.v1} {v2} a y') = lem-⊂-distinct v1 v2 dist y'
  
----------------------------------------------------------------------------
--  Deletes a given element a from vector v, provided a proof of a ∈ v.
--
--  Only the first occurence is removed.
----------------------------------------------------------------------------

delete : {A : Set} {n : ℕ} → (a : A) → (v : Vec A (suc n)) → a ∈ v → Vec A n
delete a (.a ∷ xs)    here         = xs
delete a (y ∷ [])     (there x∈xs) = []
delete a (y ∷ x ∷ xs) (there x∈xs) = y ∷ delete a (x ∷ xs) x∈xs

-- properties of delete:

lem-delete-others : {A : Set} {n : ℕ} {a : A} {v : Vec A (suc n)} (p : a ∈ v) 
                  → (eq : Decidable {A = A} _≡_) → (b : A) → a ≢ b 
                  → b ∈ v → b ∈ delete a v p
lem-delete-others {A} {n} {.a} {a ∷ xs} here eq .a a≢b here = ⊥-elim (a≢b refl)
lem-delete-others {A} {n} {.a} {a ∷ xs} here eq b a≢b (there x∈xs) = x∈xs
lem-delete-others {A} {.0} {a} {y ∷ []} (there ()) eq b a≢b inn
lem-delete-others {a = a} {v = y ∷ x ∷ xs} (there x∈xs) eq .y a≢b here = here
lem-delete-others {a = a} {v = y ∷ x ∷ xs} (there x∈xs) eq b a≢b (there x∈xs') = there (lem-delete-others x∈xs eq b a≢b x∈xs')

lem-delete-others-inv : {A : Set} {n : ℕ} {a : A} {v : Vec A (suc n)} (p : a ∈ v) 
                      → (eq : Decidable {A = A} _≡_) → (b : A) → a ≢ b 
                      → b ∈ delete a v p → b ∈ v 
lem-delete-others-inv {A} {n} {.x} {x ∷ xs} here eq b a≢b b∈del = there b∈del
lem-delete-others-inv {A} {.0} {a} {x ∷ []} (there x∈xs) eq b a≢b ()
lem-delete-others-inv {a = a} {v = x ∷ x' ∷ xs} (there x∈xs) eq .x a≢b here = here
lem-delete-others-inv {a = a} {v = x ∷ x' ∷ xs} (there x∈xs) eq b a≢b (there x∈xs') = there (lem-delete-others-inv x∈xs eq b a≢b x∈xs')


lem-others-stay : {A : Set} {n : ℕ} (a : A) (v : Vec A (suc n)) (p : a ∈ v) 
                  → distinct-v v → a ∉ delete a v p
lem-others-stay a .(a ∷ xs) (here {n} {.a} {xs}) (dist-cons dist y) a∈delete = y a∈delete
lem-others-stay a .(y ∷ []) (there {.0} {.a} {y} {[]} x∈xs) (dist-cons dist y') ()
lem-others-stay .y (y ∷ .y ∷ xs) (there here) (dist-cons (dist-cons dist y') y0) here = y0 here
lem-others-stay .x (y ∷ x ∷ xs) (there here) (dist-cons (dist-cons dist y') y0) (there x∈xs) = y' x∈xs
lem-others-stay .y (y ∷ x ∷ xs) (there (there x∈xs)) (dist-cons (dist-cons dist y') y0) here = y0 (there x∈xs)
lem-others-stay a (y ∷ x ∷ xs) (there (there x∈xs)) (dist-cons (dist-cons dist y') y0) (there x∈xs') 
  = lem-others-stay a (x ∷ xs) (there x∈xs) (dist-cons dist y') x∈xs'


lem-subvector-delete : {A : Set} {n : ℕ} (a : A) (v : Vec A (suc n)) (p : a ∈ v) 
                     →  delete a v p ⊂ v
lem-subvector-delete .a (a ∷ xs) here = there a (lem-⊂-refl xs)
lem-subvector-delete a (y ∷ []) (there ())
lem-subvector-delete a (y ∷ x ∷ xs) (there x∈xs) = here y (lem-subvector-delete a (x ∷ xs) x∈xs)


lem-delete-distinct-is-distinct : {A : Set} {n : ℕ} (a : A) (v : Vec A (suc n)) (p : a ∈ v) 
                                →  distinct-v v → distinct-v (delete a v p)
lem-delete-distinct-is-distinct a v p x = lem-⊂-distinct (delete a v p) v x (lem-subvector-delete a v p)

---------------------------
--  Vector permutations  --
---------------------------

infix 3 _≈_

data _≈_ {l}{A : Set l} : ∀ {n} → Vec A n → Vec A n → Set l where

  nil : [] ≈ []

  swp : ∀ {a b n} {Γ : Vec A n} 
      → a ∷ b ∷ Γ ≈ b ∷ a ∷ Γ

  cns : ∀ {a n} {Γ Γ' : Vec A n} 
      → Γ ≈ Γ' 
      → a ∷ Γ ≈ a ∷ Γ'

  trn : ∀ {n}{Γ1 Γ2 Γ3 : Vec A n} 
      → Γ1 ≈ Γ2 
      → Γ2 ≈ Γ3
      → Γ1 ≈ Γ3


perm-reflexive : ∀ {l}{A : Set l} → {n : ℕ} → (Γ : Vec A n) 
               → Γ ≈ Γ
perm-reflexive []       = nil
perm-reflexive (x ∷ xs) = cns (perm-reflexive xs)


perm-symmetric : ∀ {l}{A : Set l} → {n : ℕ} → {Γ Γ' : Vec A n} 
               → Γ  ≈ Γ' 
               → Γ' ≈ Γ
perm-symmetric nil        = nil
perm-symmetric swp        = swp
perm-symmetric (cns x)    = cns (perm-symmetric x)
perm-symmetric (trn x x₁) = trn (perm-symmetric x₁) (perm-symmetric x)


-- each element in a permutation can be found in the other vector at some position

perm-lookup : ∀ {l}{A : Set l}{n}
            → {Γ Γ' : Vec A n}
            → {x : A}
            → (i : Fin n)
            → Γ ≈ Γ'
            → lookup i Γ ≡ x
            → Σ[ j ∶ Fin n ](lookup j Γ' ≡ x)

perm-lookup () nil eq
perm-lookup zero          swp eq = suc zero , eq
perm-lookup (suc zero)    swp eq = zero , eq
perm-lookup (suc (suc i)) swp eq = suc (suc i) , eq
perm-lookup zero (cns perm) eq = zero , eq
perm-lookup (suc i) (cns perm) eq with perm-lookup i perm eq
... | j , rec = suc j , rec
perm-lookup i (trn perm1 perm2) eq with perm-lookup i perm1 eq
... | j , rec = perm-lookup j perm2 rec


-- preimage of a permutation pair is a permutation pair
{-
perm-map-inv : 
             → map f v1 ≈ map f v2
             → v1 ≈ v2
-}
