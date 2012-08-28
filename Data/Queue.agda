{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)

  Queues indexed by size.
-}
module Data.Queue where

open import Coinduction

open import Data.List hiding ([_])
open import Data.Nat
open import Data.Vec renaming (reverse to vreverse)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Data.Nat.Theorems


{-
Implementation idea:

The simplest implementation uses two lists, front and rear, with the property that front ++ reverse rear 
would give all elements in the queue in the reverse order they were inserted. For example: after enqueue 1, 
enqueue 2, enqueue 3 we might have front = [1], rear = [3,2]. The basic idea is that dequeue will operate on 
the front and enqueue will operate on the rear - so we can use the lists efficiently. The only “problem” arises
when front becomes empty - we have to reverse the rear then.

To simplify life, Okasaki managed an invariant: if the queue is not empty then front is not empty. In Agda we want
to know even more - we want to index the queue by the number of it’s element. Therefore we use two vectors instead
of two lists. To make it easier to access both the element and the rest of the queue we use a view, with can 
be reified only(!) if the queue is not empty.

Unfortunately, we have to clutter the code with coersions on the index level, but it’s only visible in the implementation. 
(It was worse in the code I wrote at first, but using rewrite instead of subst is a big improvement).
-}

------------------------
--  Queue operations  --
------------------------

data Queue (A : Set) : ℕ → Set where
  empty     : Queue A 0
  non-empty : {k n m : ℕ} → (fr : Vec A (suc n)) → (bk : Vec A m) → (eq : n + m ≡ k) → Queue A (suc k)

infixl 5 _▸_
infixr 5 _◂_

-- adding an element on the right

_▸_ : {A : Set} {n : ℕ} → Queue A n → A → Queue A (suc n)
empty                            ▸ a = non-empty [ a ] []       refl
(non-empty {k} {n} {m} fr bk eq) ▸ a = non-empty fr    (a ∷ bk) $
  begin 
    n + suc m   ≡⟨ sym (lem-plus-s n m) ⟩ 
    suc (n + m) ≡⟨ cong suc eq ⟩ 
    suc k 
  ∎

-- the view from the left

data viewL (A : Set) : ℕ → Set where
  _◂_ : {n : ℕ} → (a : A) → (q : Queue A n) → viewL A n

getView : {A : Set} {n : ℕ} → Queue A (suc n) → viewL A n
getView (non-empty (x ∷ [])      []        eq) rewrite sym eq = x ◂ empty
getView (non-empty (x ∷ [])      (x' ∷ xs) eq) rewrite sym eq = x ◂ non-empty (vreverse (x' ∷ xs)) [] (lem-plus-n-0 _)
getView (non-empty (x ∷ x' ∷ xs) bk        eq) rewrite sym eq = x ◂ non-empty (x' ∷ xs) bk refl

-- singleton queue

⟨_⟩ : {A : Set} → A → Queue A 1
⟨ a ⟩ = empty ▸ a
