module Nat where

open import Eq

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
infixl 7 _×_

_+_ : ℕ → ℕ → ℕ
Z + n     = n
(S k) + n = S(k + n)

{-# BUILTIN NATPLUS _+_ #-}

_×_ : ℕ → ℕ → ℕ
Z  × n = Z
S m × n = n + m × n

{-# BUILTIN NATTIMES _×_ #-}

*-right-zero : ∀ (n : ℕ) → n × Z ≡ Z
*-right-zero Z = Refl
*-right-zero (S n) = *-right-zero n

testEq : (x : ℕ) → (y : ℕ) → (p : x ≡ y) → ℕ
testEq x _ Refl = x
