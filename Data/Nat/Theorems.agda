module Data.Nat.Theorems where

open import Data.Nat hiding (compare)
open import Data.Nat.Compare
open import Data.Sum

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

{- 
   ----------------------------------
       Properties of addition (_+_) 
   ----------------------------------
-}

lem-plus-0-n : (n : ℕ) → 0 + n ≡ n
lem-plus-0-n n = refl

lem-plus-n-0 : (n : ℕ) → n + 0 ≡ n
lem-plus-n-0 zero    = refl
lem-plus-n-0 (suc n) = cong suc (lem-plus-n-0 n)

lem-plus-1-n : (n : ℕ) → 1 + n ≡ n + 1
lem-plus-1-n zero = refl
lem-plus-1-n (suc n) = cong suc (lem-plus-1-n n)

lem-plus-s : (n m : ℕ) → suc (n + m) ≡ n + suc m
lem-plus-s zero m = refl
lem-plus-s (suc n) m = cong suc (lem-plus-s n m)

lem-plus-comm : (n m : ℕ) → n + m ≡ m + n
lem-plus-comm zero m = sym (lem-plus-n-0 m)
lem-plus-comm (suc n) m = trans (cong suc (lem-plus-comm n m)) (lem-plus-s m n)

lem-plus-assoc : (k l n : ℕ) → (k + l) + n ≡ k + (l + n)
lem-plus-assoc zero l n = refl
lem-plus-assoc (suc n) l n' = cong suc (lem-plus-assoc n l n')

{- 
  ----------------------------------------
     Properties of multiplication (_*_)
  ----------------------------------------
-}

lem-mult-0-n : (n : ℕ) → 0 * n ≡ 0
lem-mult-0-n n = refl

lem-mult-n-0 : (n : ℕ) → n * 0 ≡ 0
lem-mult-n-0 zero = refl
lem-mult-n-0 (suc n) = lem-mult-n-0 n

lem-mult-1-n : (n : ℕ) → 1 * n ≡ n
lem-mult-1-n n = lem-plus-n-0 n

lem-mult-n-1 : (n : ℕ) → n * 1 ≡ n
lem-mult-n-1 zero = refl
lem-mult-n-1 (suc n) = cong suc (lem-mult-n-1 n)

lem-mult-plus : (k n m : ℕ) → (k + n) * m ≡ k * m + n * m
lem-mult-plus zero n m = refl
lem-mult-plus (suc k) n m = trans (cong (λ x → m + x) (lem-mult-plus k n m)) (sym (lem-plus-assoc m (k * m) (n * m)))

lem-mult-assoc : (k n m : ℕ) → (k * n) * m ≡ k * (n * m)
lem-mult-assoc zero n m = refl
lem-mult-assoc (suc k) n m = trans (lem-mult-plus n (k * n) m) (cong (λ x → n * m + x) (lem-mult-assoc k n m))

{-
  ---------------------------------
       Even and odd predicates
  ---------------------------------
-}

data Even : ℕ → Set where
  ev-0 : Even 0
  ev-s : forall {n} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  odd : ∀ {n} → Even n → Odd (suc n)

lem-plus-of-evens : ∀ {n m} → Even n → Even m → Even (n + m)
lem-plus-of-evens ev-0 p2 = p2
lem-plus-of-evens (ev-s p1) p2 = ev-s (lem-plus-of-evens p1 p2)

lem-plus-of-odds : ∀ {n m} → Odd n → Odd m → Even (n + m)
lem-plus-of-odds {suc n} {suc m} (odd p1) (odd p2) = subst Even (cong suc (lem-plus-s n m) ) (ev-s (lem-plus-of-evens p1 p2))
lem-plus-of-odds {m = zero} _ ()
lem-plus-of-odds {n = zero} () _

lem-twice-is-even : ∀ n → Even (n + n)
lem-twice-is-even zero = ev-0
lem-twice-is-even (suc n) = subst Even (cong suc (lem-plus-s n n)) (ev-s (lem-twice-is-even n))

lem-mult-of-evens-l : ∀ {n m} → Even n → Even (n * m)
lem-mult-of-evens-l {.zero} ev-0 = ev-0
lem-mult-of-evens-l {suc (suc n)} {m} (ev-s y) = subst Even (lem-plus-assoc m m (n * m)) (lem-plus-of-evens (lem-twice-is-even m) (lem-mult-of-evens-l y))

lem-mult-of-odds : ∀ {n m} → Odd n → Odd m → Odd (n * m)
lem-mult-of-odds {suc n} {suc m} (odd y) (odd y') = odd (lem-plus-of-evens y' (lem-mult-of-evens-l y))
lem-mult-of-odds {zero} () _
lem-mult-of-odds {n} {zero} _ ()

lem-square-of-evens : ∀ {n} → Even n → Even (n * n)
lem-square-of-evens p = lem-mult-of-evens-l p

lem-square-of-odds : ∀ {n} → Odd n → Odd (n * n)
lem-square-of-odds p = lem-mult-of-odds p p


lem-odd-or-even : ∀ n → Even n ⊎ Odd n
lem-odd-or-even zero = inj₁ ev-0
lem-odd-or-even (suc n) with lem-odd-or-even n
...                            | inj₁ p = inj₂ (odd p)
lem-odd-or-even (suc .(suc n)) | inj₂ (odd {n} y) = inj₁ (ev-s y)

{-
  ------------------------------
           A parity view
  ------------------------------
-}

data Parity : ℕ → Set where
  odd  : (k : ℕ) → Parity (1 + k * 2)
  even : (k : ℕ) → Parity (k * 2)

getParity : (n : ℕ) → Parity n
getParity zero = even zero
getParity (suc n) with getParity n
getParity (suc .(suc (k * 2))) |  odd k = even (suc k)
getParity (suc .(k * 2))       | even k = odd k


{-
  ------------------------------
    Properties of (my) compare
  ------------------------------
-}

EQ≠LT : EQ ≢ LT
EQ≠LT ()

EQ≠GT : EQ ≢ GT
EQ≠GT ()

LT≠EQ : LT ≢ EQ
LT≠EQ ()

LT≠GT : LT ≢ GT
LT≠GT ()

GT≠LT : GT ≢ LT
GT≠LT ()

GT≠EQ : GT ≢ EQ
GT≠EQ ()

lem-compare-refl : (n : ℕ) → compare n n ≡ EQ
lem-compare-refl zero    = refl
lem-compare-refl (suc n) = lem-compare-refl n

lem-compare-swap : ∀ {m n} → compare m n ≡ GT → compare n m ≡ LT
lem-compare-swap {zero} {zero} ()
lem-compare-swap {zero} {suc n} ()
lem-compare-swap {suc m} {zero} p = refl
lem-compare-swap {suc m} {suc n} p = lem-compare-swap {m = m} p

lem-compare-trans-lt : ∀ {m n l} → compare m n ≡ LT → compare n l ≡ LT → compare m l ≡ LT
lem-compare-trans-lt {zero} {zero} {l} mn nl = nl
lem-compare-trans-lt {(suc n)} {zero} {l} () nl
lem-compare-trans-lt {m} {(suc n)} {zero} mn ()
lem-compare-trans-lt {zero} {(suc n)} {(suc n')} mn nl = refl
lem-compare-trans-lt {(suc m)} {(suc n')} {(suc n0)} mn nl = lem-compare-trans-lt {m = m} mn nl

lem-compare-eq : ∀ {n m} → compare n m ≡ EQ → n ≡ m
lem-compare-eq {zero} {zero} p = refl
lem-compare-eq {zero} {suc n} ()
lem-compare-eq {suc n} {zero} ()
lem-compare-eq {suc n} {suc n'} p = cong suc (lem-compare-eq p)


{-
  -----------------------------------
       Properties of ⊔ and <
  -----------------------------------
-}

lem-≤-trans : Transitive _≤_
lem-≤-trans = Poset.trans (DecTotalOrder.poset decTotalOrder)

lem-≤-suc : ∀ (n : ℕ) → n ≤ suc n
lem-≤-suc zero = z≤n
lem-≤-suc (suc n) = s≤s (lem-≤-suc n)

lem-<-trans : Transitive _<_
lem-<-trans {j = suc n} (s≤s m≤n) (s≤s n≤k) = s≤s (lem-≤-trans (lem-≤-trans m≤n (lem-≤-suc n)) n≤k)
lem-<-trans {j = zero} () p2

lem-⊔ : ∀ (n m : ℕ) → n ⊔ m ≡ n ⊎ n ⊔ m ≡ m
lem-⊔ zero m = inj₂ refl
lem-⊔ (suc n) zero = inj₁ refl
lem-⊔ (suc n) (suc n') with lem-⊔ n n' 
lem-⊔ (suc n) (suc n') | inj₁ x = inj₁ (cong suc x)
lem-⊔ (suc n) (suc n') | inj₂ y = inj₂ (cong suc y)

lem-≤-l+ : ∀ (m p q : ℕ) → m ≤ q → m ≤ p + q
lem-≤-l+ m zero q pr = pr
lem-≤-l+ .0 (suc n) q z≤n = z≤n
lem-≤-l+ .(suc m) (suc n) .(suc n') (s≤s {m} {n'} m≤n) = s≤s (≤-cong (lem-≤-l+ m (suc n) n' m≤n) (lem-plus-s n n')) where
  ≤-cong : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
  ≤-cong x<=y refl = x<=y

lem-≤-+r : ∀ (m p q : ℕ) → m ≤ q → m ≤ q + p
lem-≤-+r .0 n q z≤n = z≤n
lem-≤-+r .(suc m) zero .(suc n) (s≤s {m} {n} m≤n) = s≤s (lem-≤-+r m zero n m≤n)
lem-≤-+r .(suc m) (suc n) .(suc n') (s≤s {m} {n'} m≤n) = s≤s (lem-≤-+r m (suc n) n' m≤n)


lem-<-cong : ∀ {n m p q} → n < p → m < q → (n ⊔ m) < p + q
lem-<-cong {n} {m} p1 p2 with lem-⊔ n m 
lem-<-cong {n} {m} {p} {q} p1 p2 | inj₁ x rewrite x = lem-≤-+r (suc n) q p p1
lem-<-cong {n} {m} {p} {q} p1 p2 | inj₂ y rewrite y = lem-≤-l+ (suc m) p q p2