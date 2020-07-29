module Chapter2.Section2 where

open import Level using (Level)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe as M using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (does)

private
  variable a : Level

-- Definition of tree
data Tree (α : Set a) : Set a where
  leaf : Tree α
  node : (l : Tree α) (x : α) (r : Tree α) → Tree α

-- The number of nodes in a tree
size : {α : Set a} → Tree α → ℕ
size leaf = zero
size (node a _ b) = suc (size a + size b)

-- Definition of balanced tree
data Balanced {α : Set a} : Tree α → Set a where
  bleaf  : Balanced leaf
  bequal : {a b : Tree α} {x : α} → Balanced a → Balanced b → size a ≡ size b       → Balanced (node a x b)
  bleft  : {a b : Tree α} {x : α} → Balanced a → Balanced b → size a ≡ suc (size b) → Balanced (node a x b)
  bright : {a b : Tree α} {x : α} → Balanced a → Balanced b → suc (size a) ≡ size b → Balanced (node a x b)

-- Implementation of a BST as in figure 2.9
module UnbalancedSet
  {ℓ₁ ℓ₂ : Level} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

  open StrictTotalOrder strictTotalOrder renaming (Carrier to α)

  member : α → Tree α → Bool
  member x leaf = false
  member x (node a y b) =
    if does (x <? y) then member x a
    else if does (y <? x) then member x b
    else true

  insert : α → Tree α → Tree α
  insert x leaf = node leaf x leaf
  insert x s@(node a y b) =
    if does (x <? y) then node (insert x a) y b
    else if does (y <? x) then node a y (insert x b)
    else s

-- Reduce the number of comparisons in member
module Exercise2
  {ℓ₁ ℓ₂ : Level} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

  open StrictTotalOrder strictTotalOrder renaming (Carrier to α)

  member′ : α → Tree α → Bool
  member′ x = helper nothing
    where
      helper : Maybe α → Tree α → Bool
      helper nothing leaf = false
      helper (just c) leaf = does (c ≟ x)
      helper c (node a y b) =
        if does (x <? y) then helper c a
        else helper (just y) b

-- Avoid unnecessary copying in insert
module Exercise3
  {ℓ₁ ℓ₂ : Level} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

  open UnbalancedSet strictTotalOrder
  open StrictTotalOrder strictTotalOrder renaming (Carrier to α)

  insert′ : α → Tree α → Tree α
  insert′ x t = M.fromMaybe t (helper t)
    where
      helper : Tree α → Maybe (Tree α)
      helper leaf = just (node leaf x leaf)
      helper (node a y b) =
        if does (x <? y) then M.map (λ t → node t y b) (helper a)
        else if does (y <? x) then M.map (λ t → node a y t) (helper b)
        else nothing

-- Avoid unnecessary copying and reduce number of comparisons in insert
module Exercise4
  {ℓ₁ ℓ₂ : Level} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

  open StrictTotalOrder strictTotalOrder renaming (Carrier to α)

  insert″ : α → Tree α → Tree α
  insert″ x t = M.fromMaybe t (helper nothing t)
    where
    helper : Maybe α → Tree α → Maybe (Tree α)
    helper nothing leaf = just (node leaf x leaf)
    helper (just c) leaf =
      if does (c ≟ x) then nothing
      else just (node leaf x leaf)
    helper c (node a y b) =
      if does (x <? y) then M.map (λ t → node t y b) (helper c a)
      else M.map (λ t → node a y t) (helper (just y) b)

module Exercise5a where
  -- f x d returns a complete binary tree of depth d consisting only x's
  f : {α : Set a} → α → ℕ → Tree α
  f x zero = leaf
  f x (suc d) = node (f x d) x (f x d)

module Exercise5b where
  open import Data.Nat using (_≤_; z≤n; s≤s; _<_)
  open import Data.Nat.Properties using (+-suc; ≤-trans; n≤1+n)
  open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
  open import Data.Product as P using (_×_; _,_; proj₁; proj₂)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (refl; cong; sym; trans)

  -- Auxiliary function to split a Nat evenly
  splitEven : ℕ → ℕ × ℕ
  splitEven 0 = 0 , 0
  splitEven 1 = 0 , 1
  splitEven (suc (suc n)) = P.map suc suc (splitEven n)

  lemma₁ : (n : ℕ) → proj₁ (splitEven n) ≤ n
  lemma₁ 0 = z≤n
  lemma₁ 1 = z≤n
  lemma₁ (suc (suc n)) with lemma₁ n
  ... | h = s≤s (≤-trans h (n≤1+n n))

  lemma₂ : (n : ℕ) → proj₂ (splitEven n) ≤ n
  lemma₂ 0 = z≤n
  lemma₂ 1 = s≤s z≤n
  lemma₂ (suc (suc n)) with lemma₂ n
  ... | h = s≤s (≤-trans h (n≤1+n n))

  f′ : {α : Set a} → α → (n : ℕ) → Acc _<_ n → Tree α
  f′ x 0 (acc rec) = leaf
  f′ x (suc n) (acc rec) with splitEven n | lemma₁ n | lemma₂ n
  ... | a , b | h₁ | h₂  = node (f′ x a (rec a (s≤s h₁))) x (f′ x b (rec b (s≤s h₂)))

  -- f x n returns a balanced binary tree of size n consisting only x's
  f : {α : Set a} → α → (n : ℕ) → Tree α
  f x n = f′ x n (<-wellFounded n)

  lemma₃ : (n : ℕ) → P.uncurry _+_ (splitEven n) ≡ n
  lemma₃ 0 = refl
  lemma₃ 1 = refl
  lemma₃ (suc (suc n)) with splitEven n | lemma₃ n
  ... | a , b | h rewrite +-suc a b = cong (λ x → suc (suc x)) h

  lemma₄ : {α : Set a} (x : α) {n : ℕ} (ac : Acc _<_ n) → size (f′ x n ac) ≡ n
  lemma₄ x {zero} (acc _) = refl
  lemma₄ x {suc n} (acc rec)
    rewrite lemma₄ x {proj₁ (splitEven n)} (rec _ (s≤s (lemma₁ n))) |
            lemma₄ x {proj₂ (splitEven n)} (rec _ (s≤s (lemma₂ n)))
            = cong suc (lemma₃ n)

  -- f x n has size n
  theorem₁ : {α : Set a} (x : α) (n : ℕ) → size (f x n) ≡ n
  theorem₁ x n = lemma₄ x (<-wellFounded n)

  lemma₅ : (n : ℕ) → proj₁ (splitEven n) ≡ proj₂ (splitEven n) ⊎ suc (proj₁ (splitEven n)) ≡ proj₂ (splitEven n)
  lemma₅ 0 = inj₁ refl
  lemma₅ 1 = inj₂ refl
  lemma₅ (suc (suc n)) with lemma₅ n
  ... | inj₁ h = inj₁ (cong suc h)
  ... | inj₂ h = inj₂ (cong suc h)

  lemma₆ : {α : Set a} (x : α) {n : ℕ} (ac : Acc _<_ n) → Balanced (f′ x n ac)
  lemma₆ x {zero} (acc _) = bleaf
  lemma₆ x {suc n} (acc rec) with lemma₅ n
  ... | inj₁ h = bequal (lemma₆ x (rec _ (s≤s (lemma₁ n))))
                        (lemma₆ x (rec _ (s≤s (lemma₂ n))))
                        (trans (trans (lemma₄ x (rec _ (s≤s (lemma₁ n)))) h) (sym (lemma₄ x (rec _ (s≤s (lemma₂ n))))))
  ... | inj₂ h = bright (lemma₆ x (rec _ (s≤s (lemma₁ n))))
                        (lemma₆ x (rec _ (s≤s (lemma₂ n))))
                        (trans (trans (cong suc (lemma₄ x (rec _ (s≤s (lemma₁ n))))) h) (sym (lemma₄ x (rec _ (s≤s (lemma₂ n))))))

  -- f x n is balanced
  theorem₂ : {α : Set a} (x : α) (n : ℕ) → Balanced (f x n)
  theorem₂ x n = lemma₆ x (<-wellFounded n)
