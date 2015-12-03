module Cryptol where

open import Bool
open import Nat
open import Eq

postulate
  Int    : Set
  Float  : Set
  Char   : Set
  String : Set

{-# BUILTIN INTEGER Int    #-}
{-# BUILTIN FLOAT   Float  #-}
{-# BUILTIN CHAR    Char   #-}
{-# BUILTIN STRING  String #-}


data List (A : Set) : Set where
  Nil  : List A
  Cons : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL Nil #-}
{-# BUILTIN CONS Cons #-}

append : {A : Set} → List A → List A → List A
append Nil ys         = ys
append (Cons x xs) ys = Cons x (append xs ys)

infixr 5 _::_

data Vec (A : Set) : ℕ → Set where
  Nil  : Vec A Z
  _::_ : {n : ℕ} → A → Vec A n → Vec A (S n)

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
Nil       ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Bit : Set where
  O : Bit
  I : Bit

Word : ℕ → Set
Word n = Vec Bit n

data SnocView {A : Set} : List A → Set where
  Nil : SnocView Nil
  Snoc : (xs : List A) → (x : A) → SnocView (append xs (Cons x Nil))

view : {A : Set} → (xs : List A) → SnocView xs
view Nil = Nil
view (Cons x xs) with view xs
view (Cons x _)      | Nil = Snoc Nil x
view (Cons x _)      | Snoc ys y = Snoc (Cons x ys) y

rotateRight : {A : Set} → List A → List A
rotateRight xs with view xs
rotateRight _ | Nil       = Nil
rotateRight _ | Snoc ys y = Cons y ys

take : ∀ {A m} → (n : ℕ) → Vec A (n + m) → Vec A n
take Z l             = Nil
take (S k) (x :: xs) = x :: take k xs

drop : ∀ {A m} → (n : ℕ) → Vec A (n + m) → Vec A m
drop Z xs            = xs
drop (S k) (x :: xs) = drop k xs

split : ∀ {A} → (n : ℕ) → (m : ℕ) → Vec A (m × n) → Vec (Vec A n) m
split n Z     Nil = Nil
split n (S k) xs  = (take n xs) :: (split n k (drop n xs))

concat : ∀ {A n m} → Vec (Vec A n) m → Vec A (m × n)
concat Nil = Nil
concat (xs :: xss) = xs ++ concat xss

postulate
  splitConcatLemma : ∀ {A : Set} → (m : ℕ) → (n : ℕ) → (xs : Vec A (m × n)) → concat (split n m xs) ≡ xs

takeDropLemma : ∀ {A : Set} → (n : ℕ) → (m : ℕ) → (xs : Vec A (n + m)) → ((take n xs) ++ (drop n xs)) ≡ xs
takeDropLemma Z m _ = Refl
takeDropLemma (S k) m (x :: xs) with ((take k xs) ++ (drop k xs)) | takeDropLemma k _ xs
takeDropLemma (S k) m (x :: xs) | ._ | Refl = Refl


data SplitView {A : Set} : {n : ℕ} → (m : ℕ) → Vec A (m × n) → Set where
 [_] : ∀ {m n} → (xss : Vec (Vec A n) m) → SplitView m (concat xss)

splitView : {A : Set} → (n : ℕ) → (m : ℕ) → (xs : Vec A (m × n)) → SplitView m xs
splitView n m xs with concat (split n m xs) | [ split n m xs ] | splitConcatLemma m n xs
splitView n m xs | _ | v | Refl = v


data TakeView (A : Set) (m : ℕ) (n : ℕ) : Vec A (m + n) → Set where
  Take : (xs : Vec A m) → (ys : Vec A n) → TakeView A m n (xs ++ ys)

--sv : {A : Set} → (n : ℕ) → (m : ℕ) → Vec a

swab : Word 32 → Word 32
swab xs with splitView 8 4 xs
swab _ | [ a :: b :: c :: d :: Nil ] = concat (b :: a :: c :: d :: Nil)
 
