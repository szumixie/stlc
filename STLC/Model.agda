module STLC.Model where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import Data.Nat

private variable n : Nat

record Model : Type₂ where
  no-eta-equality
  infixl 40 _∘_ _[_]
  infixl 4 _▸_ _,_
  field
    Con : Type₁
    Sub : Con → Con → Type
    Sub-is-set : ∀ {Δ Γ} → is-set (Sub Δ Γ)

    _∘_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    assoc :
      ∀ {Γ Δ Θ Ξ} (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) →
      γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ

    id : ∀ {Γ} → Sub Γ Γ
    idr : ∀ {Γ Δ} (γ : Sub Δ Γ) → γ ∘ id ≡ γ
    idl : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≡ γ

    Ty : Type₁
    Tm : Con → Ty → Type
    Tm-is-set : ∀ {Γ A} → is-set (Tm Γ A)

    _[_] : ∀ {Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    []-∘ :
      ∀ {Γ Δ Θ A} (a : Tm Γ A) (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
      a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
    []-id : ∀ {Γ A} (a : Tm Γ A) → a [ id ] ≡ a

    _▸_ : Con → Ty → Con
    p : ∀ {Γ A} → Sub (Γ ▸ A) Γ
    q : ∀ {Γ A} → Tm (Γ ▸ A) A

    _,_ : ∀ {Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▸ A)
    ,-∘ :
      ∀ {Γ Δ Θ A} (γ : Sub Δ Γ) (a : Tm Δ A) (δ : Sub Θ Δ) →
      (γ , a) ∘ δ ≡ (γ ∘ δ , a [ δ ])

    ▸-β₁ : ∀ {Γ Δ A} (γ : Sub Δ Γ) (a : Tm Δ A) → p ∘ (γ , a) ≡ γ
    ▸-β₂ : ∀ {Γ Δ A} (γ : Sub Δ Γ) (a : Tm Δ A) → q [ γ , a ] ≡ a
    ▸-η : ∀ {Γ A} → (p , q) ≡ id {Γ ▸ A}

    ◆ : Con
    ε : ∀ {Γ} → Sub Γ ◆
    ε-∘ : ∀ {Γ Δ} (γ : Sub Δ Γ) → ε ∘ γ ≡ ε
    ◆-η : ε ≡ id

  infixl 4 _↑
  _↑ : ∀ {Γ Δ A} → Sub Δ Γ → Sub (Δ ▸ A) (Γ ▸ A)
  γ ↑ = γ ∘ p , q

  ⟨_⟩ : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ ▸ A)
  ⟨_⟩ = id ,_

  infixr 0 _⇒_
  field
    _⇒_ : Ty → Ty → Ty
    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    app-[] :
      ∀ {Γ Δ A B} (f : Tm Γ (A ⇒ B)) a (γ : Sub Δ Γ) →
      app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▸ A) B → Tm Γ (A ⇒ B)
    lam-[] :
      ∀ {Γ Δ A B} (b : Tm (Γ ▸ A) B) (γ : Sub Δ Γ) →
      lam b [ γ ] ≡ lam (b [ γ ↑ ])

    ⇒-β : ∀ {Γ A B} (b : Tm (Γ ▸ A) B) a → app (lam b) a ≡ b [ ⟨ a ⟩ ]
    ⇒-η : ∀ {Γ A B} (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

    ⊥ : Ty
    ⊥-rec : ∀ {Γ A} → Tm Γ ⊥ → Tm Γ A
    ⊥-rec-[] :
      ∀ {Γ Δ A} t (γ : Sub Δ Γ) → ⊥-rec {A = A} t [ γ ] ≡ ⊥-rec (t [ γ ])

    Bool : Ty
    true : ∀ {Γ} → Tm Γ Bool
    true-[] : ∀ {Γ Δ} (γ : Sub Δ Γ) → true [ γ ] ≡ true
    false : ∀ {Γ} → Tm Γ Bool
    false-[] : ∀ {Γ Δ} (γ : Sub Δ Γ) → false [ γ ] ≡ false

    Bool-rec : ∀ {Γ A} → Tm Γ A → Tm Γ A → Tm Γ Bool → Tm Γ A
    Bool-rec-[] :
      ∀ {Γ Δ A} (a₁ a₂ : Tm Γ A) t (γ : Sub Δ Γ) →
      Bool-rec a₁ a₂ t [ γ ] ≡ Bool-rec (a₁ [ γ ]) (a₂ [ γ ]) (t [ γ ])

    Bool-β₁ : ∀ {Γ A} (a₁ a₂ : Tm Γ A) → Bool-rec a₁ a₂ true ≡ a₁
    Bool-β₂ : ∀ {Γ A} (a₁ a₂ : Tm Γ A) → Bool-rec a₁ a₂ false ≡ a₂

  instance
    H-Level-Sub : ∀ {Δ Γ} → H-Level (Sub Δ Γ) (2 + n)
    H-Level-Sub = basic-instance 2 Sub-is-set

    H-Level-Tm : ∀ {Γ A} → H-Level (Tm Γ A) (2 + n)
    H-Level-Tm = basic-instance 2 Tm-is-set
