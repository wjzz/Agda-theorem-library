{-# OPTIONS --universe-polymorphism #-}

module Data.List.Theorems where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Theorems
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- support for equational reasoning
open ≡-Reasoning -- \qed, ≡⟨ ⟩ \==\<


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

{- A membership relation -}

infix 4 _∈_

data _∈_ {A : Set} : (a : A) → (xs : List A) → Set where
  ∈-take : (a : A)   → (xs : List A) → a ∈ a ∷ xs
  ∈-drop : (a x : A) → (xs : List A) → a ∈ xs → a ∈ x ∷ xs

-- if equality is decidable for A then list membership is decidable
member : {A : Set} → (a : A) → (l : List A) → Decidable {A = A} (_≡_) → Dec(a ∈ l)
member a [] eq = no (λ ())
member a (x ∷ xs) eq with inspect (eq a x)
member a (x ∷ xs) eq | yes p with-≡ eq' rewrite p = yes (∈-take x xs) 
member a (x ∷ xs) eq | no ¬p with-≡ eq' with member a xs eq
member a (x ∷ xs) eq | no ¬p with-≡ eq' | yes p = yes (∈-drop a x xs p)
member a (x ∷ xs) eq | no ¬p' with-≡ eq' | no ¬p = no (imp a x xs ¬p ¬p') where
  imp : {A : Set}(a x : A)(xs : List A) → (¬ a ∈ xs) → (¬ a ≡ x) → ¬ a ∈ x ∷ xs
  imp .x' x' xs' ¬axs ¬ax (∈-take .x' .xs') = ¬ax refl
  imp a' x' xs' ¬axs ¬ax (∈-drop .a' .x' .xs' y) = ¬axs y
