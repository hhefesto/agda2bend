{-# OPTIONS --without-K --safe #-}
module A2bRec where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

id : {l : Level} {A : Set l} → A → A
id a = a

_~_ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (f g : (x : A) → B x) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

tr : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A} → x ＝ y → B x → B y
tr B refl b = b

module _ {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3} where

  tot : (f : (x : A) → B x → C x) → Σ A B → Σ A C
  tot f (pair x y) = pair x (f x y)

tot-id : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) → tot (λ x (y : B x) → y) ~ id
tot-id B (pair x y) = refl

eq-pair-Σ :
  {l1 l2 : Level} {A : Set l1} {B : A → Set l2} {s t : Σ A B}
  (α : pr1 s ＝ pr1 t) → tr B α (pr2 s) ＝ pr2 t → s ＝ t
eq-pair-Σ {s = pair x y} {pair .x .y} refl refl = refl

eta-Σ : {l1 l2 : Level} {A : Set l1} {B : A → Set l2} (s : Σ A B) → pair (pr1 s) (pr2 s) ＝ s
eta-Σ s = refl

swap-swap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (s : Σ A (λ _ → B)) →
  pair (pr1 (pair (pr2 s) (pr1 s))) (pr2 (pair (pr2 s) (pr1 s))) ＝ pair (pr2 s) (pr1 s)
swap-swap (pair a b) = refl

-- agda-unimath's shapes: no record pattern, the goal needs eta
tot-id' : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) → tot (λ x (y : B x) → y) ~ id
tot-id' B p = refl

preserves-comp-tot :
  {l1 l2 l3 l4 : Level} {A : Set l1} {B : A → Set l2} {B' : A → Set l3} {B'' : A → Set l4}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x y → g x (f x y)) ~ (λ s → tot g (tot f s))
preserves-comp-tot f g p = refl

record unit : Set where
  constructor star

center-unit : (x : unit) → star ＝ x
center-unit x = refl

eq-pair' : {l1 l2 : Level} {A : Set l1} {B : Set l2} (s t : Σ A (λ _ → B)) →
  pr1 s ＝ pr1 t → pr2 s ＝ pr2 t → s ＝ t
eq-pair' s t refl refl = refl
