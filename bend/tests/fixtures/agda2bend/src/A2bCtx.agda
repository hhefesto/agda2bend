-- agda2bend fixture (2026-10-29): indices that are constructors (Γ , B ∋
-- A at Z {.Γ} {.A}, plfa's ext): the fields Agda dots are bound, the
-- index equation splits into one a field, and a function parameter whose
-- type mentions a dotted outer variable is read transported (rename's ρ,
-- used twice in app); ⇒-inj₁/₂ and ▸-inj split a refl pattern's equation.
module A2bCtx where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Type : Set where
  ★ : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → (Γ , A) ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A B} → (Γ , B) ∋ A → (Δ , B) ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

data Ty : Set where
  `ℕ  : Ty
  _⇒_ : Ty → Ty → Ty

data Ctx : Set where
  ε   : Ctx
  _▸_ : Ctx → Ty → Ctx

data _∈_ : Ty → Ctx → Set where
  here  : ∀ {Γ A} → A ∈ (Γ ▸ A)
  there : ∀ {Γ A B} → A ∈ Γ → A ∈ (Γ ▸ B)

ext′ : ∀ {Γ Δ} → (∀ {A} → A ∈ Γ → A ∈ Δ) → (∀ {A B} → A ∈ (Γ ▸ B) → A ∈ (Δ ▸ B))
ext′ ρ here      = here
ext′ ρ (there x) = there (ρ x)

dom : Ty → Ty
dom `ℕ = `ℕ
dom (A ⇒ B) = A

lookup-dom : ∀ {Γ A B} → (A ⇒ B) ∈ Γ → Ty
lookup-dom {A = A} here = A
lookup-dom {A = A} (there x) = A

⇒-inj₁ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
⇒-inj₁ refl = refl

⇒-inj₂ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
⇒-inj₂ refl = refl

▸-inj : ∀ {Γ Δ A B} → (Γ ▸ A) ≡ (Δ ▸ B) → A ≡ B
▸-inj refl = refl

data Lam : Ctx → Ty → Set where
  var : ∀ {Γ A} → A ∈ Γ → Lam Γ A
  abs : ∀ {Γ A B} → Lam (Γ ▸ A) B → Lam Γ (A ⇒ B)
  app : ∀ {Γ A B} → Lam Γ (A ⇒ B) → Lam Γ A → Lam Γ B

rename : ∀ {Γ Δ} → (∀ {A} → A ∈ Γ → A ∈ Δ) → ∀ {A} → Lam Γ A → Lam Δ A
rename ρ (var x)   = var (ρ x)
rename ρ (abs N)   = abs (rename (ext′ ρ) N)
rename ρ (app L M) = app (rename ρ L) (rename ρ M)
