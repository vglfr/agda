module PLFA.P1-1-Naturals where

data N : Set where
  nil  : N
  succ : N -> N
