{-# OPTIONS --without-K --safe #-}
module A2bTpl where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1
open Σ public

_∘_ :
  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : (a : A) → B a → Set l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)

module _ {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} where
  is-inv : Set (l1 ⊔ l2)
  is-inv = Σ (B → A) (λ g → Σ ((y : B) → f (g y) ＝ y) (λ _ → (x : A) → g (f x) ＝ x))

  map-inv : is-inv → B → A
  map-inv H = pr1 H

  sec : (H : is-inv) (y : B) → f (map-inv H y) ＝ y
  sec H = pr1 (pr2 H)

  ret : (H : is-inv) (x : A) → map-inv H (f x) ＝ x
  ret H = pr2 (pr2 H)

  -- H used three times, through defs: a template parameter in Bend
  re : is-inv → is-inv
  re H = pair (map-inv H) (pair (sec H) (ret H))

  -- its eta-expansion passes a lambda's variable to re's template: the
  -- combinator-unfolded alternative, re (re H), is the one that checks
  re2 : is-inv → is-inv
  re2 = re ∘ re
