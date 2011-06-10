{-# OPTIONS --universe-polymorphism #-}

module Data.List.Theorems where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Theorems
open import Data.List
open import Data.Product 

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- support for equational reasoning
open ≡-Reasoning -- \qed, ≡⟨ ⟩ \==\<

{- BASE global ⊥-elim sym trans -}

{- length properties -}

lem-length-app : ∀ {A : Set} → (l1 l2 : List A) → length (l1 ++ l2) ≡ length l1 + length l2
lem-length-app [] l2 = refl
lem-length-app (x ∷ xs) l2 = cong suc (lem-length-app xs l2)


{- ++ properties -}

lem-app-l-nil : ∀ {A : Set}(l : List A) → l ++ [] ≡ l
lem-app-l-nil [] = refl
lem-app-l-nil (x ∷ xs) = cong (λ l → x ∷ l) (lem-app-l-nil xs)

lem-app-assoc : ∀ {A : Set}(l1 l2 l3 : List A) → l1 ++ (l2 ++ l3) ≡ (l1 ++ l2) ++ l3
lem-app-assoc [] l2 l3 = refl
lem-app-assoc (x ∷ xs) l2 l3 = cong (λ l → x ∷ l) (lem-app-assoc xs l2 l3)


{- frev properties (auxillary lemmas for reverse -}

-- a crucial function for proving anything about reverse, 
-- as reverse = frev []
frev : {A : Set} (l1 l2 : List A) → List A
frev = foldl (λ rev x → x ∷ rev)

lem-foldl-app : ∀ {A : Set}(l1 l2 l3 : List A) → frev (l3 ++ l1) l2 ≡ frev l3 l2 ++ l1
lem-foldl-app l1 [] l3 = refl
lem-foldl-app l1 (x ∷ xs) l3 = lem-foldl-app l1 xs (x ∷ l3)

lem-foldl-app-rev : ∀ {A : Set}(l1 l2 : List A) → frev l1 l2 ≡ reverse l2 ++ l1
lem-foldl-app-rev l1 l2 = lem-foldl-app l1 l2 []


{- reverse properties -}

lem-reverse-head : ∀ {A : Set} (x : A) (xs : List A) → reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
lem-reverse-head x xs = lem-foldl-app-rev (x ∷ []) xs

lem-reverse-len : ∀ {A : Set} → (l : List A) → length (reverse l) ≡ length l
lem-reverse-len [] = refl
lem-reverse-len (x ∷ xs) = begin 
                            length (reverse (x ∷ xs))             ≡⟨ cong length (lem-reverse-head x xs) ⟩
                            length (reverse xs ++ (x ∷ []))       ≡⟨ lem-length-app (reverse xs) (x ∷ []) ⟩ 
                            length (reverse xs) + length (x ∷ []) ≡⟨ sym (lem-plus-1-n (length (reverse xs))) ⟩ 
                            1 + length (reverse xs)               ≡⟨ cong suc (lem-reverse-len xs) ⟩ 
                            length (x ∷ xs) ∎

lem-reverse-app : ∀ {A : Set} → (l1 l2 : List A) → reverse (l1 ++ l2) ≡ reverse l2 ++ reverse l1
lem-reverse-app [] l2       = sym (lem-app-l-nil (reverse l2))
lem-reverse-app (x ∷ l1) l2 = begin 
                               reverse ((x ∷ l1) ++ l2)                ≡⟨ lem-reverse-head x (l1 ++ l2) ⟩ 
                               reverse (l1 ++ l2) ++ (x ∷ [])          ≡⟨ cong (λ l → l ++ (x ∷ [])) (lem-reverse-app l1 l2) ⟩ 
                               (reverse l2 ++ reverse l1) ++ (x ∷ [])  ≡⟨ sym (lem-app-assoc (reverse l2) (reverse l1) (x ∷ [])) ⟩ 
                                reverse l2 ++ (reverse l1 ++ (x ∷ [])) ≡⟨ cong (λ l → reverse l2 ++ l) (sym (lem-reverse-head x l1)) ⟩ 
                               (reverse l2 ++ reverse (x ∷ l1)) ∎ 

------------------------------------------
--  List membership relation and query  --
------------------------------------------


infix 4 _∈_

data _∈_ {A : Set} : (a : A) → (xs : List A) → Set where
  ∈-take : {a : A}   {xs : List A} → a ∈ a ∷ xs
  ∈-drop : {a x : A} {xs : List A} → a ∈ xs → a ∈ x ∷ xs

lem-neq-ncons-inn : {A : Set} → (a x : A)(xs : List A) → (¬ a ∈ xs) → (¬ a ≡ x) → ¬ a ∈ x ∷ xs
lem-neq-ncons-inn .x' x' xs' ¬axs ¬ax ∈-take = ¬ax refl
lem-neq-ncons-inn a' x' xs' ¬axs ¬ax (∈-drop y) = ¬axs y

-- if equality is decidable for A then list membership is decidable

member : {A : Set} → (a : A) → (l : List A) → (eq : Decidable {A = A} _≡_) → Dec(a ∈ l)
member a [] eq = no (λ ())
member a (x ∷ xs) eq with inspect (eq a x)
member a (x ∷ xs) eq | yes p with-≡ eq' rewrite p = yes ∈-take
member a (x ∷ xs) eq | no ¬p with-≡ eq' with member a xs eq
member a (x ∷ xs) eq | no ¬p with-≡ eq'  | yes p = yes (∈-drop p)
member a (x ∷ xs) eq | no ¬p' with-≡ eq' | no ¬p = no (lem-neq-ncons-inn a x xs ¬p ¬p')


----------------------------------------
--  List subset relation and queries  --
----------------------------------------

infix 4 _⊂_

data _⊂_ {A : Set} : (l1 l2 : List A) → Set where
  nil  : {l : List A} → [] ⊂ l
  cons : {m : A} {ms l : List A} → ms ⊂ l → m ∈ l → m ∷ ms ⊂ l

lem-⊂-cons-inv-tail : ∀ {A : Set}(x : A)(xs ys : List A) → (x ∷ xs ⊂ ys) → xs ⊂ ys
lem-⊂-cons-inv-tail x xs ys (cons y y') = y  

lem-⊂-cons-inv-head : ∀ {A : Set}(x : A)(xs ys : List A) → (x ∷ xs ⊂ ys) → x ∈ ys
lem-⊂-cons-inv-head x xs ys (cons y y') = y'

lem-subset-alt : ∀ {A : Set}(x : A)(xs ys : List A) → (xs ⊂ ys) → x ∈ xs → x ∈ ys
lem-subset-alt x .(x ∷ xs) ys (cons y y') (∈-take {.x} {xs}) = y'
lem-subset-alt x .(x' ∷ xs) ys xs⊂ys (∈-drop {.x} {x'} {xs} y) = lem-subset-alt x xs ys (lem-⊂-cons-inv-tail x' xs ys xs⊂ys) y

lem-⊂-ext : ∀ {A : Set}(x : A)(xs ys : List A) → xs ⊂ ys → xs ⊂ x ∷ ys
lem-⊂-ext x .[] ys nil = nil
lem-⊂-ext x .(m ∷ ms) ys (cons {m} {ms} y y') = cons (lem-⊂-ext x ms ys y) (∈-drop y')

{- BASE subset lem-⊂-cons-inv-head lem-⊂-cons-inv-tail lem-subset-alt lem-⊂-ext -}

⊂-refl : ∀ {A : Set}(xs : List A) → xs ⊂ xs
⊂-refl [] = nil
⊂-refl (x ∷ xs) = cons (lem-⊂-ext x xs xs (⊂-refl xs)) ∈-take

⊂-trans : ∀ {A : Set}(xs ys zs : List A) → xs ⊂ ys → ys ⊂ zs → xs ⊂ zs
⊂-trans .[] ys zs nil yz = nil
⊂-trans .(m ∷ ms) ys zs (cons {m} {ms} y y') yz = cons (⊂-trans ms ys zs y yz) (lem-subset-alt m ys zs yz y')

{- BASE subset ⊂-refl ⊂-trans -}

subsetDec : {A : Set} (xs ys : List A) → (eq : Decidable {A = A} _≡_) → Dec (xs ⊂ ys)
subsetDec [] ys eq = yes nil
subsetDec (x ∷ xs) ys eq with subsetDec xs ys eq
subsetDec (x ∷ xs) ys eq | yes p with member x ys eq
subsetDec (x ∷ xs) ys eq | yes p' | yes p = yes (cons p' p)
subsetDec (x ∷ xs) ys eq | yes p  | no ¬p = no (λ x' → ¬p (lem-⊂-cons-inv-head x xs ys x'))
subsetDec (x ∷ xs) ys eq | no ¬p = no (λ x' → ¬p (lem-⊂-cons-inv-tail x xs ys x'))

--------------------------------------------------------------------------------
--  Existence of a elem in a list with a certain property relation and query  --
--------------------------------------------------------------------------------

data Any {A : Set} : (P : A → Set) → (l : List A) → Set₁ where
  any-this  : {P : A → Set}{a : A}{l : List A} → P a     → Any P (a ∷ l)
  any-other : {P : A → Set}{a : A}{l : List A} → Any P l → Any P (a ∷ l)
  
lem-any-exists : {A : Set} (P : A → Set) (l : List A) → Any P l → ∃ (λ (a : A) → a ∈ l × P a)
lem-any-exists P .(a ∷ l)      (any-this  {.P} {a} {l} y) = a , ∈-take , y
lem-any-exists P .(a ∷ [])     (any-other {.P} {a} {[]} ())
lem-any-exists P .(a ∷ x ∷ xs) (any-other {.P} {a} {x ∷ xs} y) with lem-any-exists P (x ∷ xs) y
lem-any-exists P .(a ∷ x ∷ xs) (any-other {.P} {a} {x ∷ xs} y) | a0 , inn , Pa0 = a0 , ∈-drop inn , Pa0

lem-any-exists-inv : {A : Set} (P : A → Set) (l : List A) → ∃ (λ (a : A) → a ∈ l × P a) → Any P l
lem-any-exists-inv P .(a0 ∷ xs) (a0 , ∈-take {.a0} {xs} , Pa0)       = any-this Pa0
lem-any-exists-inv P .(x ∷ xs)  (a0 , ∈-drop {.a0} {x} {xs} y , Pa0) = any-other (lem-any-exists-inv P xs (a0 , y , Pa0))

lem-none-exists : {A : Set} (P : A → Set) (l : List A) → ¬ Any P l → ¬ ∃ (λ (a : A) → a ∈ l × P a)
lem-none-exists P l x x' = x (lem-any-exists-inv P l x')


lem-any-nhead-ncons-nlist : {A : Set} (P : A → Set) (a : A)(xs : List A) → (¬ P a) → (¬ Any P xs) → ¬ Any P (a ∷ xs)
lem-any-nhead-ncons-nlist P a xs ¬Pa ¬Pxs (any-this y)  = ¬Pa y
lem-any-nhead-ncons-nlist P a xs ¬Pa ¬Pxs (any-other y) = ¬Pxs y

{- BASE any lem-any-nhead-ncons-nlist lem-any-exists lem-none-exists -}

any-dec : {A : Set} (P : A → Set) (l : List A) → ((a : A) → Dec (P a)) → Dec (Any P l)
any-dec P [] decP = no (λ ())
any-dec P (x ∷ xs) decP with decP x
any-dec P (x ∷ xs) decP | yes p = yes (any-this p)
any-dec P (x ∷ xs) decP | no ¬p with any-dec P xs decP
any-dec P (x ∷ xs) decP | no ¬p  | yes p = yes (any-other p)
any-dec P (x ∷ xs) decP | no ¬p' | no ¬p = no (lem-any-nhead-ncons-nlist P x xs ¬p' ¬p)

------------------------
--  Certified filter  --
------------------------

filterDec : {A : Set} {P : A → Set} → (l : List A) → (decP : ((a : A) → Dec (P a))) → List A
filterDec [] decP = []
filterDec (x ∷ xs) decP with decP x
filterDec (x ∷ xs) decP | yes p = x ∷ filterDec xs decP
filterDec (x ∷ xs) decP | no ¬p = filterDec xs decP


filterDec-valid : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) → P a →
                                          a ∈ l → a ∈ filterDec l decP
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) with decP a
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) | yes p = ∈-take
filterDec-valid .(a ∷ xs) decP a Pa (∈-take {.a} {xs}) | no ¬p = ⊥-elim (¬p Pa)
filterDec-valid .(x ∷ xs) decP a Pa (∈-drop {.a} {x} {xs} y) with decP x
... | yes p = ∈-drop (filterDec-valid xs decP a Pa y)
... | no ¬p = filterDec-valid xs decP a Pa y


filterDec-valid-rev : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) →
                                               a ∈ filterDec l decP → a ∈ l × P a
filterDec-valid-rev [] decP a ()
filterDec-valid-rev (x ∷ xs) decP a a∈filter with decP x
filterDec-valid-rev (x ∷ xs) decP .x ∈-take | yes p = ∈-take , p
filterDec-valid-rev (x ∷ xs) decP a (∈-drop y) | yes p with filterDec-valid-rev xs decP a y
... | a∈l , Pa = ∈-drop a∈l , Pa
filterDec-valid-rev (x ∷ xs) decP a a∈filter | no ¬p with filterDec-valid-rev xs decP a a∈filter
filterDec-valid-rev (x ∷ xs) decP a a∈filter | no ¬p | a∈l , Pa = ∈-drop a∈l , Pa

{- BASE filter filterDec-valid-rev filterDec-valid -}

--------------------------------
--  Certified dual to filter  --
--------------------------------

removeDec : {A : Set} {P : A → Set} → (l : List A) → (decP : ((a : A) → Dec (P a))) → List A
removeDec [] decP = []
removeDec (x ∷ xs) decP with decP x
removeDec (x ∷ xs) decP | yes p = removeDec xs decP
removeDec (x ∷ xs) decP | no ¬p = x ∷ removeDec xs decP

removeDec-valid : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) → ¬ P a →
                                          a ∈ l → a ∈ removeDec l decP
removeDec-valid .(a ∷ xs) decP a ¬Pa (∈-take {.a} {xs}) with decP a
... | yes p = ⊥-elim (¬Pa p)
... | no ¬p = ∈-take
removeDec-valid .(x ∷ xs) decP a ¬Pa (∈-drop {.a} {x} {xs} y) with decP x
... | yes p = removeDec-valid xs decP a ¬Pa y
... | no ¬p = ∈-drop (removeDec-valid xs decP a ¬Pa y)

removeDec-valid-rev : {A : Set} {P : A → Set} (l : List A) (decP : ((a : A) → Dec (P a))) → (a : A) →
                                               a ∈ removeDec l decP → a ∈ l × ¬ P a
removeDec-valid-rev [] decP a ()
removeDec-valid-rev (x ∷ xs) decP a a∈remove with decP x
... | yes p with removeDec-valid-rev xs decP a a∈remove
removeDec-valid-rev (x ∷ xs) decP a a∈remove | yes p | a∈l , ¬Pa = ∈-drop a∈l , ¬Pa
removeDec-valid-rev (x ∷ xs) decP .x ∈-take  | no ¬p = ∈-take , ¬p
removeDec-valid-rev (x ∷ xs) decP a (∈-drop y) | no ¬p with removeDec-valid-rev xs decP a y
... | a∈l , ¬Pa = ∈-drop a∈l , ¬Pa

{- BASE remove removeDec-valid-rev removeDec-valid -}