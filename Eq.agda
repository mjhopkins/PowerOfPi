module Eq where

infix 4 _≡_

{-
data _≡_ {A : Set} : A → A → Set where
  Refl : {x : A} → x ≡ x
-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  Refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL Refl #-}
