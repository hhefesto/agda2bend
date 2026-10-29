{-# OPTIONS --cubical-compatible #-}
-- agda2bend fixture (2026-10-29): the clauses --cubical-compatible
-- generates beside a match on refl are left out (≤-reflexive); an
-- equation between successors rewrites under a2b_pred (pred-cancel); an
-- impossible case of a def whose type ends in ¬ A takes no extra argument
-- (invertⁿ); a projection of a constructor value is its field (map′'s does
-- after its proof clauses split the Dec).
module A2bInj where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

≤-reflexive : ∀ {m n} → m ≡ n → m ≤ n
≤-reflexive {zero}  refl = z≤n
≤-reflexive {suc m} refl = s≤s (≤-reflexive refl)

pred-cancel : ∀ {m n} → suc m ≡ suc n → m ≡ n
pred-cancel refl = refl

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Reflects (A : Set) : Bool → Set where
  ofʸ : ( a :   A) → Reflects A true
  ofⁿ : (¬a : ¬ A) → Reflects A false

record Dec (A : Set) : Set where
  constructor _because_
  field
    does  : Bool
    proof : Reflects A does
open Dec public

invertʸ : {A : Set} → Reflects A true → A
invertʸ (ofʸ a) = a

invertⁿ : {A : Set} → Reflects A false → ¬ A
invertⁿ (ofⁿ ¬a) = ¬a

map′ : {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
does  (map′ A→B B→A a?) = does a?
proof (map′ A→B B→A (true  because  [a])) = ofʸ (A→B (invertʸ [a]))
proof (map′ A→B B→A (false because [¬a])) = ofⁿ (λ b → invertⁿ [¬a] (B→A b))
