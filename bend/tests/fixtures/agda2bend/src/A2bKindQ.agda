{-# OPTIONS --without-K #-}
module A2bKindQ where

open import Agda.Primitive

data L {a} (A : Set a) : Set a where
  nil : L A
  cons : A → L A → L A

data Less {a} {A : Set a} (lt : A → A → Set a) : L A → L A → Set a where
  here : ∀ {x y xs ys} → lt x y → Less lt (cons x xs) (cons y ys)
  there : ∀ {x xs ys} → Less lt xs ys → Less lt (cons x xs) (cons x ys)

record Box {a} (A : Set a) : Set a where
  field
    inner : L A

record Fns {a} (A : Set a) : Set a where
  field
    run : A → L A
