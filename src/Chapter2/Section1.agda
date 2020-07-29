module Chapter2.Section1 where

open import Level using (Level)
open import Agda.Builtin.Bool
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)

private
  variable a : Level

infixr 5 _∷_

data List (α : Set a) : Set a where
  [] : List α
  _∷_ : (x : α) (xs : List α) → List α

null : {α : Set} → List α → Bool
null [] = true
null (_ ∷ _) = false

head : {α : Set} → List α → Maybe α
head [] = nothing
head (x ∷ _) = just x

tail : {α : Set} → List α → Maybe (List α)
tail [] = nothing
tail (_ ∷ xs) = just xs

infixr 5 _++_

_++_ : {α : Set} → List α → List α → List α
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

update : {α : Set} → List α → ℕ → α → List α
update [] n y = []
update (x ∷ xs) zero y = y ∷ xs
update (x ∷ xs) (suc n) y = x ∷ (update xs n y)

module Exercise1 where
  suffixes : {α : Set} → List α → List (List α)
  suffixes [] = [] ∷ []
  suffixes x@(y ∷ ys) = x ∷ suffixes ys

  test1 : List (List ℕ)
  test1 = suffixes (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
