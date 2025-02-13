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

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

_ : inc ⟨⟩ ≡ ⟨⟩ I
_ =
  begin
    inc ⟨⟩
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    (inc ⟨⟩) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ =
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    (⟨⟩ I) I
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ =
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    ((inc ⟨⟩) O) O
  ≡⟨⟩
    ((⟨⟩ I) O) O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

to : N -> Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O
_ =
  begin
    to 0
  ≡⟨⟩
    ⟨⟩ O
  ∎

_ : to 1 ≡ ⟨⟩ I
_ =
  begin
    to 1
  ≡⟨⟩
    inc (to 0)
  ≡⟨⟩
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : to 2 ≡ ⟨⟩ I O
_ =
  begin
    to 2
  ≡⟨⟩
    inc (to 1)
  ≡⟨⟩
    inc (inc (to 0))
  ≡⟨⟩
    inc (inc (⟨⟩ O))
  ≡⟨⟩
    inc (⟨⟩ I)
  ≡⟨⟩
    (inc ⟨⟩) O
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : to 3 ≡ ⟨⟩ I I
_ =
  begin
    to 3
  ≡⟨⟩
    inc (to 2)
  ≡⟨⟩
    inc (inc (to 1))
  ≡⟨⟩
    inc (inc (inc (to 0)))
  ≡⟨⟩
    inc (inc (inc (⟨⟩ O)))
  ≡⟨⟩
    inc (inc (⟨⟩ I))
  ≡⟨⟩
    inc ((inc ⟨⟩) O)
  ≡⟨⟩
    inc (⟨⟩ I O)
  ≡⟨⟩
    (⟨⟩ I) I
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : to 4 ≡ ⟨⟩ I O O
_ =
  begin
    to 4
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (inc (to 2))
  ≡⟨⟩
    inc (inc (inc (to 1)))
  ≡⟨⟩
    inc (inc (inc (inc (to 0))))
  ≡⟨⟩
    inc (inc (inc (inc (⟨⟩ O))))
  ≡⟨⟩
    inc (inc (inc (⟨⟩ I)))
  ≡⟨⟩
    inc (inc ((inc ⟨⟩) O))
  ≡⟨⟩
    inc (inc (⟨⟩ I O))
  ≡⟨⟩
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    ((inc ⟨⟩) O) O
  ≡⟨⟩
    ((⟨⟩ I) O) O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

{-
  8 = 1000
    = 1*2^3 + 0*2^2 + 0*2^1 + 0*2^0
    =   8   +   0   +   0   +   0

  13 = 1101
     = 1*2^3 + 1*2^2 + 0*2^1 + 1*2^0
     =   8   +   4   +   0   +   1

  13 = 1101'
     = 2 * 110' + 1
     = 2 * (2 * 11') + 1
     = 2 * (2 * (2 * 1' + 1)) + 1
     = 2 * (2 * (2 * (2 * 0 + 1) + 1)) + 1
     = 2 * (2 * (2 * 1 + 1)) + 1
     = 2 * (2 * 3) + 1
     = 2 * 6 + 1
     = 13
-}

from : Bin -> N
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = 2 * from b + 1

_ : from ⟨⟩ ≡ 0
_ =
  begin
    from ⟨⟩
  ≡⟨⟩
    0
  ∎

_ : from (⟨⟩ O) ≡ 0
_ =
  begin
    from (⟨⟩ O)
  ≡⟨⟩
    2 * (from ⟨⟩)
  ≡⟨⟩
    2 * 0
  ≡⟨⟩
    0
  ∎

_ : from (⟨⟩ I) ≡ 1
_ =
  begin
    from (⟨⟩ I)
  ≡⟨⟩
    2 * (from ⟨⟩) + 1
  ≡⟨⟩
    2 * 0 + 1
  ≡⟨⟩
    1
  ∎

_ : from (⟨⟩ I O) ≡ 2
_ =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩
    2 * from (⟨⟩ I)
  ≡⟨⟩
    2 * (2 * from ⟨⟩ + 1)
  ≡⟨⟩
    2 * (2 * 0 + 1)
  ≡⟨⟩
    2 * 1
  ≡⟨⟩
    2
  ∎

_ : from (⟨⟩ I I) ≡ 3
_ =
  begin
    from (⟨⟩ I I)
  ≡⟨⟩
    2 * from (⟨⟩ I) + 1
  ≡⟨⟩
    2 * (2 * from ⟨⟩ + 1) + 1
  ≡⟨⟩
    2 * (2 * 0 + 1) + 1
  ≡⟨⟩
    2 * 1 + 1
  ≡⟨⟩
    3
  ∎

_ : from (⟨⟩ I O O) ≡ 4
_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    2 * from (⟨⟩ I O)
  ≡⟨⟩
    2 * (2 * from (⟨⟩ I))
  ≡⟨⟩
    2 * (2 * (2 * from ⟨⟩ + 1))
  ≡⟨⟩
    2 * (2 * (2 * 0 + 1))
  ≡⟨⟩
    2 * 2 * 1
  ≡⟨⟩
    4
  ∎
