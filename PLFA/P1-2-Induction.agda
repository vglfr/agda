module PLFA.P1-2-Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identity-r : ∀ (m : ℕ) -> m + zero ≡ m
+-identity-r zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identity-r (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identity-r m) ⟩
    suc m
  ∎

+-identity-l : ∀ (m : ℕ) -> zero + m ≡ m
+-identity-l m = refl

+-suc : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity-r m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) -> (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎

+-assoc' : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) -> n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) -> m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

+-assoc'' : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc'' zero n p = refl
+-assoc'' (suc m) n p rewrite +-assoc'' m n p = refl

*-distrib-r-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-r-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero + n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-r-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-r-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-zero-r : ∀ (n : ℕ) -> n * zero ≡ zero
*-zero-r zero = refl
*-zero-r (suc n) rewrite *-zero-r n = refl

-- *-distrib-l-+ : ∀ (m n p : ℕ) -> m * (n + p) ≡ m * n + m * p
-- *-distrib-l-+ m n zero =
--   begin
--     m * (n + zero)
--   ≡⟨ cong (m *_) (+-identity-r n) ⟩
--     m * n
--   ≡⟨ sym (+-identity-r (m * n)) ⟩
--     m * n + zero
--   ≡⟨ cong (m * n +_) (sym (*-zero-r m)) ⟩
--     m * n + m * zero
--   ∎
-- *-distrib-l-+ m n (suc p) =
--   begin
--     m * (n + suc p)
--   ≡⟨ (m *_) (+-comm n (suc p)) ⟩
--     m * (suc p + n)
--   ≡⟨⟩
--     m * suc (p + n)
--   ≡⟨ (m * suc _) (+-comm n p) ⟩
--     m * suc (n + p)
--   ≡⟨⟩
--     m * (n + p) + m
--   ≡⟨ cong (_+ m) (*-distrib-l-+ m n p) ⟩
--     (m * n + m * p) + m
--   ≡⟨ +-assoc (m * n) (m * p) m ⟩
--     m * n + (m * p + m)
--   ≡⟨⟩
--     m * n + m * suc p
--   ∎

*-distrib-l-+ : ∀ (m n p : ℕ) -> m * (n + p) ≡ m * n + m * p
*-distrib-l-+ zero n p = refl
*-distrib-l-+ (suc m) n p =
  begin
    suc m * (n + p)
  ≡⟨ cong (_* (n + p)) (sym (+-identity-r m)) ⟩
    (m + suc zero) * (n + p)
  ≡⟨ *-distrib-r-+ m (suc zero) (n + p) ⟩
    (m * (n + p)) + (suc zero * (n + p))
  ≡⟨ cong _+_ (*-distrib-l-+ m n p) refl ⟩
    (m * n + m * p) + (n + p)
  ≡⟨ +-comm (m * n + m * p) (n + p) ⟩
    (n + p) + (m * n + m * p)
  ≡⟨ +-comm n (m * n) ⟩
    n + m * n + p + m * p
  ≡⟨⟩
    suc m * n + suc m * p
  ∎

*-assoc : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
  ≡⟨⟩
    zero * p
  ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-r-+ n (m * n) p ⟩
    (n * p) + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + m * (n * p)
  ≡⟨⟩
    (suc zero + m) * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎

*-identity-r : ∀ (m : ℕ) -> m * suc zero ≡ m
*-identity-r zero =
  begin
    zero * suc zero
  ≡⟨⟩
    zero
  ∎
*-identity-r (suc m) =
  begin
    suc m * suc zero
  ≡⟨⟩
    suc (m * suc zero)
  ≡⟨ cong suc (*-identity-r m) ⟩
    suc m
  ∎

*-identity-l : ∀ (m : ℕ) ->  suc zero * m ≡ m
*-identity-l zero =
  begin
    suc zero * zero
  ≡⟨⟩
    zero
  ∎
*-identity-l (suc m) =
  begin
    suc zero * suc m
  ≡⟨⟩
    suc (suc zero * m)
  ≡⟨ cong suc (*-identity-l m) ⟩
    suc m
  ∎

_ : 1 * 0 ≡ 0
_ =
  begin
    1 * 0
  ≡⟨⟩
    0
  ∎

*-suc-r : ∀ (m n : ℕ) -> m * suc n ≡ m * n + m -- a*3 = a*2 + a 
*-suc-r zero n = refl
*-suc-r (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    suc m * (suc zero + n)
  ≡⟨ *-distrib-l-+ (suc m) (suc zero) n ⟩
    suc m * suc zero + suc m * n
  ≡⟨ +-comm (suc m * suc zero) (suc m * n) ⟩
    suc m * n + suc m * suc zero
  ≡⟨ cong (suc m * n +_) (*-identity-r (suc m)) ⟩
    suc m * n + suc m
  ∎

*-suc-l : ∀ (m n : ℕ) -> suc m * n ≡ m * n + n -- 3*a = 2*a + a
*-suc-l zero n =
  begin
    suc zero * n
  ≡⟨ *-identity-l n ⟩
    n
  ≡⟨⟩
    zero + n
  ≡⟨⟩
    zero * n + n
  ∎
*-suc-l (suc m) n =
  begin
    suc (suc m) * n
  ≡⟨⟩
    (suc zero + suc m) * n
  ≡⟨ *-distrib-r-+ (suc zero) (suc m) n ⟩
    suc zero * n + suc m * n
  ≡⟨ +-comm (suc zero * n) (suc m * n) ⟩
    suc m * n + suc zero * n
  ≡⟨ cong (suc m * n +_) (*-identity-l n) ⟩
    suc m * n + n
  ∎

_ : 2 + 1 * 2 ≡ 2 + 2
_ =
  begin
    2 + 1 * 2
  ≡⟨⟩
    2 * 2
  ∎

*-nested-id : ∀ (m n : ℕ) -> m + suc zero * n ≡ m + n
*-nested-id zero n =
  begin
    zero + suc zero * n
  ≡⟨ +-identity-l (suc zero * n) ⟩
    suc zero * n
  ≡⟨ *-identity-l n ⟩
    n
  ≡⟨⟩
    zero + n
  ∎
-- *-nested-id (suc m) n rewrite *-identity-l n = refl
*-nested-id (suc m) n =
  begin
    suc m + suc zero * n
  ≡⟨ cong (suc m +_) (*-identity-l n) ⟩
    suc m + n
  ∎

*-nested-id-2 : ∀ (m n : ℕ) -> m * suc zero + n ≡ m + n
*-nested-id-2 zero n = refl
-- *-nested-id-2 (suc m) n rewrite *-identity-r m = refl
*-nested-id-2 (suc m) n =
  begin
    suc m * suc zero + n
  ≡⟨ cong (_+ n) (*-identity-r (suc m)) ⟩
    suc m + n
  ∎

*-comm : ∀ (m n : ℕ) -> m * n ≡ n * m
*-comm m zero =
  begin
    m * zero
  ≡⟨ *-zero-r m ⟩
    zero
  ≡⟨⟩
    zero * m
  ∎
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-suc-r m n ⟩
    m * n + m
  ≡⟨ cong (_+ m) (*-comm m n) ⟩
    n * m + m
  ≡⟨ sym (*-suc-l n m) ⟩
    suc n * m
  ∎

∸-monus : ∀ (n : ℕ) -> 0 ∸ n ≡ 0
∸-monus zero = refl
∸-monus (suc n) = refl

-- ∸-+-assoc : ∀ (m n p : ℕ) -> m ∸ n ∸ p ≡ m ∸ (n + p)
