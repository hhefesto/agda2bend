{-# OPTIONS --without-K --safe #-}
-- agda2bend's fixture for agda-unimath's shapes, second (2026-10-31): a
-- data type in Setω whose constructors take their own levels (telescope);
-- universe levels given by level functions, a type-valued definition's
-- sort at one applied (Large-Relation-Prop); unit an eta record, so
-- `inr (inl _)` is the clause of `inr (inl star)` (is-retraction-pred-ℤ).
module A2bUm where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit renaming (⊤ to unit; tt to star)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

-- telescopes

data telescope : (l : Level) → Nat → Setω where
  base-telescope : {l1 : Level} → Set l1 → telescope l1 0
  cons-telescope :
    {l1 l2 : Level} {n : Nat} {X : Set l1} →
    (X → telescope l2 n) → telescope (l1 ⊔ l2) (suc n)

prepend-telescope :
  {l1 l2 : Level} {n : Nat} →
  (A : Set l1) → ({x : A} → telescope l2 n) → telescope (l1 ⊔ l2) (suc n)
prepend-telescope A B = cons-telescope {X = A} (λ x → B {x})

apply-base-telescope :
  {l1 : Level} {n : Nat}
  (P : {l : Level} → Set l → Set l) → telescope l1 n → telescope l1 n
apply-base-telescope P (base-telescope A) = base-telescope (P A)
apply-base-telescope P (cons-telescope A) =
  cons-telescope (λ x → apply-base-telescope P (A x))

-- large relations

is-prop : {l : Level} → Set l → Set l
is-prop A = (x y : A) → x ＝ y

Prop : (l : Level) → Set (lsuc l)
Prop l = Σ (Set l) is-prop

type-Prop : {l : Level} → Prop l → Set l
type-Prop P = pr1 P

Large-Relation :
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → Set (α l)) → Setω
Large-Relation β A = {l1 l2 : Level} → A l1 → A l2 → Set (β l1 l2)

Large-Relation-Prop :
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → Set (α l)) → Setω
Large-Relation-Prop β A = {l1 l2 : Level} → A l1 → A l2 → Prop (β l1 l2)

large-relation-Large-Relation-Prop :
  {α : Level → Level} {β : Level → Level → Level} (A : (l : Level) → Set (α l)) →
  Large-Relation-Prop β A → Large-Relation β A
large-relation-Large-Relation-Prop A R x y = type-Prop (R x y)

-- integers

data _+_ {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  inl : A → A + B
  inr : B → A + B

ℤ : Set
ℤ = Nat + (unit + Nat)

succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero) = inr (inl star)
succ-ℤ (inl (suc x)) = inl x
succ-ℤ (inr (inl star)) = inr (inr zero)
succ-ℤ (inr (inr x)) = inr (inr (suc x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (suc x)
pred-ℤ (inr (inl star)) = inl zero
pred-ℤ (inr (inr zero)) = inr (inl star)
pred-ℤ (inr (inr (suc x))) = inr (inr x)

is-retraction-pred-ℤ : (x : ℤ) → pred-ℤ (succ-ℤ x) ＝ x
is-retraction-pred-ℤ (inl zero) = refl
is-retraction-pred-ℤ (inl (suc x)) = refl
is-retraction-pred-ℤ (inr (inl _)) = refl
is-retraction-pred-ℤ (inr (inr zero)) = refl
is-retraction-pred-ℤ (inr (inr (suc x))) = refl

is-section-pred-ℤ : (x : ℤ) → succ-ℤ (pred-ℤ x) ＝ x
is-section-pred-ℤ (inl zero) = refl
is-section-pred-ℤ (inl (suc x)) = refl
is-section-pred-ℤ (inr (inl _)) = refl
is-section-pred-ℤ (inr (inr zero)) = refl
is-section-pred-ℤ (inr (inr (suc x))) = refl
