module PLFA.P1-2-Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc m + (n + p)
  ∎

+-identity-r : ∀ (m : ℕ) -> m + zero ≡ m
+-identity-r zero = refl
+-identity-r (suc m) =
  begin
    suc m + zero
  ≡⟨ cong suc (+-identity-r m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) -> suc (m + n) ≡ m + suc n
+-suc zero n = refl
+-suc (suc m) n =
  begin
    suc (suc m + n)
  ≡⟨⟩
    suc (suc (m + n))
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (m + suc n)
  ≡⟨⟩
    suc m + suc n
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identity-r n) ⟩
    n + zero
  ∎
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ +-suc n m ⟩
    n + suc m
  ∎

-- *-distrib-r-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p

-- *-distrib-l-+ : ∀ (m n p : ℕ) -> m * (n + p) ≡ m * n + m * p

-- *-assoc : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)

-- *-identity-r : ∀ (m : ℕ) -> m * suc zero ≡ m

-- *-identity-l : ∀ (m : ℕ) ->  suc zero * m ≡ m

-- *-comm : ∀ (m n : ℕ) -> m * n ≡ n * m
