{-# OPTIONS --without-K --exact-split --no-postfix-projections --safe #-}
module A2bCdi where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _＝_)

_∙_ : {l : Level} {A : Set l} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
refl ∙ q = q
infixl 15 _∙_

ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) {x y : A} → x ＝ y → f x ＝ f y
ap f refl = refl

tr : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x y : A} (p : x ＝ y) → B x → B y
tr B refl b = b

dependent-identification :
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → Set l2
dependent-identification B p u v = (tr B p u ＝ v)

module _
  {l1 l2 : Level} {A : Set l1} (B : A → Set l2)
  where

  concat-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) {x' : B x} {y' : B y} {z' : B z} →
    dependent-identification B p x' y' →
    dependent-identification B q y' z' →
    dependent-identification B (p ∙ q) x' z'
  concat-dependent-identification refl q refl q' = q'

  compute-concat-dependent-identification-left-base-refl :
    { y z : A} (q : y ＝ z) →
    { x' y' : B y} {z' : B z} (p' : x' ＝ y') →
    ( q' : dependent-identification B q y' z') →
    concat-dependent-identification refl q p' q' ＝ ap (tr B q) p' ∙ q'
  compute-concat-dependent-identification-left-base-refl q refl q' = refl
