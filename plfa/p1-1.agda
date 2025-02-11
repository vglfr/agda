module plfa.p1-1 where

data N : Set where
  nil  : N
  succ : N -> N
