{-# OPTIONS --without-K --safe #-}
module A2bTele where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Agda.Builtin.Nat renaming (Nat to ℕ; suc to succ-ℕ)

data telescope : (l : Level) → ℕ → Setω where
  base-telescope : {l1 : Level} → Set l1 → telescope l1 0
  cons-telescope :
    {l1 l2 : Level} {n : ℕ} {X : Set l1} →
    (X → telescope l2 n) → telescope (l1 ⊔ l2) (succ-ℕ n)

instance-telescope⁰ : {l : Level} {X : Set l} → telescope l 0
instance-telescope⁰ {X = X} = base-telescope X

instance-telescope¹ :
  { l1 l : Level} {A1 : Set l1} {X : A1 → Set l} → telescope (l1 ⊔ l) 1
instance-telescope¹ {X = X} = cons-telescope (λ x → instance-telescope⁰ {X = X x})

instance-telescope² :
  { l1 l2 l : Level} {A1 : Set l1} {A2 : A1 → Set l2}
  { X : (x1 : A1) → A2 x1 → Set l} → telescope (l1 ⊔ l2 ⊔ l) 2
instance-telescope² {X = X} = cons-telescope (λ x → instance-telescope¹ {X = X x})

iterated-Π : {l : Level} {n : ℕ} → telescope l n → Set l
iterated-Π (base-telescope A) = A
iterated-Π (cons-telescope {X = X} A) = (x : X) → iterated-Π (A x)

iterated-implicit-Π : {l : Level} {n : ℕ} → telescope l n → Set l
iterated-implicit-Π (base-telescope A) = A
iterated-implicit-Π (cons-telescope {X = X} A) = {x : X} → iterated-implicit-Π (A x)
