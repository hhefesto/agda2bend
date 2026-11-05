{-# OPTIONS --without-K #-}
module A2bDec where

open import Agda.Builtin.Bool

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

if_then_else_ : {B : Set₁} → Bool → B → B → B
if true  then a else b = a
if false then a else b = b

data Reflects (A : Set) : Bool → Set where
  ofʸ : ( a :   A) → Reflects A true
  ofⁿ : (¬a : ¬ A) → Reflects A false

of : {A : Set} {b : Bool} → if b then A else ¬ A → Reflects A b
of {b = false} ¬a = ofⁿ ¬a
of {b = true }  a = ofʸ a

invert : {A : Set} {b : Bool} → Reflects A b → if b then A else ¬ A
invert (ofʸ  a) = a
invert (ofⁿ ¬a) = ¬a

record Dec (A : Set) : Set where
  constructor _because_
  field
    does  : Bool
    proof : Reflects A does

open Dec public

map′ : {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
does  (map′ A→B B→A a?)                   = does a?
proof (map′ A→B B→A (true  because [a]))  = of (A→B (invert [a]))
proof (map′ A→B B→A (false because [¬a])) = of (λ b → invert [¬a] (B→A b))
