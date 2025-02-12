{-# OPTIONS --exact-split #-}

module PLFA.P1-1-Naturals where

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

data N : Set where
  nil : N
  suc : N -> N

{-# BUILTIN NATURAL N #-}

_+_ : N -> N -> N
nil + n = n
suc m + n = suc (m + n)

_*_ : N -> N -> N
nil * n = nil
suc m * n = n + (m * n)

_^_ : N -> N -> N
m ^ nil = 1
m ^ suc n = m * (m ^ n)

_-_ : N -> N -> N
m - nil = m
nil - suc m = nil
suc m - suc n = m - n

infixl 6 _+_ _-_
infixl 7 _*_
infixl 8 _^_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _-_ #-}

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc (3))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4))
  ≡⟨⟩
    12
  ∎

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (1))))
  ≡⟨⟩
    81
  ∎

_ : 3 - 2 ≡ 1
_ =
  begin
    3 - 2
  ≡⟨⟩
    2 - 1
  ≡⟨⟩
    1 - 0
  ≡⟨⟩
    1
  ∎

_ : 2 - 3 ≡ 0
_ =
  begin
    2 - 3
  ≡⟨⟩
    1 - 2
  ≡⟨⟩
    0 - 1
  ≡⟨⟩
    0
  ∎

_ : 5 - 3 ≡ 2
_ =
  begin
    5 - 3
  ≡⟨⟩
    4 - 2
  ≡⟨⟩
    3 - 1
  ≡⟨⟩
    2 - 0
  ≡⟨⟩
    2
  ∎

_ : 3 - 5 ≡ 0
_ =
  begin
    3 - 5
  ≡⟨⟩
    2 - 4
  ≡⟨⟩
    1 - 3
  ≡⟨⟩
    0 - 2
  ≡⟨⟩
    0
  ∎
