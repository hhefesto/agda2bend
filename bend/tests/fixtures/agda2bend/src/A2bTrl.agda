{-# OPTIONS --without-K --safe #-}
module A2bTrl where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor _,_
  field
    pr1 : A
    pr2 : B pr1
open Σ public

data 𝕋 : Set where
  neg-two : 𝕋
  succ : 𝕋 → 𝕋

is-contr : {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

is-trunc : {l : Level} (k : 𝕋) → Set l → Set l
is-trunc neg-two A = is-contr A
is-trunc (succ k) A = (x y : A) → is-trunc k (x ＝ y)

idf : {l : Level} {X : Set l} → X → X
idf x = x

-- clauses of different lengths: the first leaves H to its body, the
-- second takes H x y (is-trunc (succ k) A opens to (x y : A) → …)
is-trunc-id : {l : Level} (k : 𝕋) (A : Set l) → is-trunc k A → is-trunc k A
is-trunc-id neg-two A = idf
is-trunc-id (succ k) A H x y = is-trunc-id k (x ＝ y) (H x y)
