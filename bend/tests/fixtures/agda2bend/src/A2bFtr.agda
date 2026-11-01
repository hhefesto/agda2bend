{-# OPTIONS --without-K --safe #-}
module A2bFtr where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)
open import Agda.Builtin.Unit using (⊤; tt)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

inv : {l : Level} {A : Set l} {x y : A} → x ＝ y → y ＝ x
inv refl = refl

_∘_ : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

_~_ : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f g : A → B) → Set (l1 ⊔ l2)
f ~ g = (x : _) → f x ＝ g x

is-contr : {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

is-contr-unit : is-contr ⊤
pr1 is-contr-unit = tt
pr2 is-contr-unit _ = refl

is-contr-unit' : is-contr ⊤
is-contr-unit' = pair tt (λ _ → refl)

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) where

  fiber : Set (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

module _ {l1 l2 l3 : Level} {X : Set l1} {A : Set l2} {B : Set l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) where

  fiber-triangle : (x : X) → fiber f x → fiber g x
  fiber-triangle .(f a) (pair a refl) = pair (h a) (inv (H a))
