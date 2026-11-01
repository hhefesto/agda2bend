{-# OPTIONS --without-K --safe #-}
module A2bCs where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

module _ {l : Level} {A : Set l} where
  inv : {x y : A} → x ＝ y → y ＝ x
  inv refl = refl

  _∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  refl ∙ q = q

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

module _ {l1 l2 : Level} {A : Set l1} (B : A → Set l2) where
  tr : {x y : A} → x ＝ y → B x → B y
  tr refl b = b

  eq-transpose-tr : {x y : A} (p : x ＝ y) {u : B x} {v : B y} → v ＝ tr p u → tr (inv p) v ＝ u
  eq-transpose-tr refl q = q

module _ {l1 l2 : Level} {A : Set l1} {B : A → Set l2} where
  eq-pair-Σ : {s t : Σ A B} (p : pr1 s ＝ pr1 t) → tr B p (pr2 s) ＝ pr2 t → s ＝ t
  eq-pair-Σ {pair x y} {pair .x .y} refl refl = refl

is-contr : {l : Level} → Set l → Set l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

module _ {l : Level} {A : Set l} where
  center : is-contr A → A
  center (pair c C) = c

  eq-is-contr : is-contr A → {x y : A} → x ＝ y
  eq-is-contr (pair c C) {x} {y} = inv (C x) ∙ C y

-- a field's helper whose type is the def's other field: pr1 of the def itself
is-torsorial-Id : {l : Level} {A : Set l} (a : A) → is-contr (Σ A (λ x → a ＝ x))
pr1 (is-torsorial-Id a) = pair a refl
pr2 (is-torsorial-Id a) (pair .a refl) = refl

module _ {l1 l2 : Level} {A : Set l1} {B : A → Set l2} where
  -- the other field is two clauses of its own
  is-contr-Σ : is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
  pr1 (pr1 (is-contr-Σ H a K)) = a
  pr2 (pr1 (is-contr-Σ H a K)) = center K
  pr2 (is-contr-Σ H a K) (pair x y) =
    eq-pair-Σ (inv (eq-is-contr H)) (eq-transpose-tr B (eq-is-contr H) (eq-is-contr K))

  -- a record pattern before the projection
  is-contr-Σ' : is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
  pr1 (pr1 (is-contr-Σ' (pair a H) K)) = a
  pr2 (pr1 (is-contr-Σ' (pair a H) K)) = center (K a)
  pr2 (is-contr-Σ' (pair a H) K) (pair x y) =
    eq-pair-Σ (inv (inv (H x))) (eq-transpose-tr B (inv (H x)) (eq-is-contr (K a)))

retraction : {l1 l2 : Level} {X : Set l1} {Y : Set l2} (f : X → Y) → Set (l1 ⊔ l2)
retraction {X = X} {Y} f = Σ (Y → X) (λ g → (x : X) → g (f x) ＝ x)

module _ {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3} where
  tot : ((x : A) → B x → C x) → Σ A B → Σ A C
  tot f (pair x y) = pair x (f x y)

  -- a pair on the right of a clause that matches after its projection
  retraction-tot : {f : (x : A) → B x → C x} → ((x : A) → retraction (f x)) → retraction (tot f)
  pr1 (retraction-tot {f} r) (pair x z) = pair x (pr1 (r x) z)
  pr2 (retraction-tot {f} r) (pair x y) = ap (pair x) (pr2 (r x) y)
