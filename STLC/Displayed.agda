module STLC.Displayed where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import Data.Nat
import STLC.Syntax as S

private variable
  n : Nat
  Γˢ Δˢ : S.Con
  γˢ γ₁ˢ γ₂ˢ δˢ θˢ : S.Sub Δˢ Γˢ
  Aˢ Bˢ : S.Ty
  aˢ a₁ˢ a₂ˢ bˢ fˢ tˢ : S.Tm Γˢ Aˢ

record Displayed : Type₂ where
  no-eta-equality
  field
    Con : S.Con → Type₁
    Sub : Con Δˢ → Con Γˢ → S.Sub Δˢ Γˢ → Type
    Sub-is-set : ∀ {Δ Γ} → is-set (Sub Δ Γ γˢ)

  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : ∀ {Δ Γ} → Sub Δ Γ γ₁ˢ → γ₁ˢ ≡ γ₂ˢ → Sub Δ Γ γ₂ˢ → Type
  _≡ˢ[_]_ {_} {_} {_} {_} {Δ} {Γ} γ₁ γ₁ˢ≡γ₂ˢ γ₂ =
    PathP (λ i → Sub Δ Γ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  infixl 40 _∘_
  field
    _∘_ : ∀ {Γ Δ Θ} → Sub Δ Γ γˢ → Sub Θ Δ δˢ → Sub Θ Γ (γˢ S.∘ δˢ)
    assoc :
      ∀ {Γ Δ Θ Ξ} (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) (θ : Sub Ξ Θ θˢ) →
      γ ∘ (δ ∘ θ) ≡ˢ[ S.assoc _ _ _ ] γ ∘ δ ∘ θ

    id : {Γ : Con Γˢ} → Sub Γ Γ S.id
    idr : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → γ ∘ id ≡ˢ[ S.idr _ ] γ
    idl : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → id ∘ γ ≡ˢ[ S.idl _ ] γ

  field
    Ty : S.Ty → Type₁
    Tm : Con Γˢ → Ty Aˢ → S.Tm Γˢ Aˢ → Type
    Tm-is-set : ∀ {Γ A} → is-set (Tm Γ A aˢ)

  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ A} → Tm Γ A a₁ˢ → a₁ˢ ≡ a₂ˢ → Tm Γ A a₂ˢ → Type
  _≡ᵗ[_]_ {_} {_} {_} {_} {Γ} {A} a₁ a₁ˢ≡a₂ˢ a₂ =
    PathP (λ i → Tm Γ A (a₁ˢ≡a₂ˢ i)) a₁ a₂

  infixl 40 _[_]
  field
    _[_] : ∀ {Γ Δ A} → Tm Γ A aˢ → Sub Δ Γ γˢ → Tm Δ A (aˢ S.[ γˢ ])
    []-∘ :
      ∀ {Γ Δ Θ A} (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) →
      a [ γ ∘ δ ] ≡ᵗ[ S.[]-∘ _ _ _ ] a [ γ ] [ δ ]
    []-id : ∀ {Γ A} (a : Tm Γ A aˢ) → a [ id ] ≡ᵗ[ S.[]-id _ ] a

  infixl 4 _▸_ _,_
  field
    _▸_ : Con Γˢ → Ty Aˢ → Con (Γˢ S.▸ Aˢ)
    p : {Γ : Con Γˢ} {A : Ty Aˢ} → Sub (Γ ▸ A) Γ S.p
    q : {Γ : Con Γˢ} {A : Ty Aˢ} → Tm (Γ ▸ A) A S.q

    _,_ : ∀ {Γ Δ A} → Sub Δ Γ γˢ → Tm Δ A aˢ → Sub Δ (Γ ▸ A) (γˢ S., aˢ)
    ,-∘ :
      ∀ {Γ Δ Θ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) (δ : Sub Θ Δ δˢ) →
      (γ , a) ∘ δ ≡ˢ[ S.,-∘ _ _ _ ] (γ ∘ δ , a [ δ ])

    ▸-β₁ :
      ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
      p ∘ (γ , a) ≡ˢ[ S.▸-β₁ _ _ ] γ
    ▸-β₂ :
      ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
      q [ γ , a ] ≡ᵗ[ S.▸-β₂ _ _ ] a
    ▸-η : {Γ : Con Γˢ} {A : Ty Aˢ} → (p , q) ≡ˢ[ S.▸-η ] id {Γ = Γ ▸ A}

    ◆ : Con S.◆
    ε : {Γ : Con Γˢ} → Sub Γ ◆ S.ε
    ε-∘ : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → ε ∘ γ ≡ˢ[ S.ε-∘ _ ] ε
    ◆-η : ε ≡ˢ[ S.◆-η ] id

  infixl 4 _↑
  _↑ : ∀ {Γ Δ} {A : Ty Aˢ} → Sub Δ Γ γˢ → Sub (Δ ▸ A) (Γ ▸ A) (γˢ S.↑)
  γ ↑ = γ ∘ p , q

  ⟨_⟩ : ∀ {Γ A} → Tm Γ A aˢ → Sub Γ (Γ ▸ A) S.⟨ aˢ ⟩
  ⟨_⟩ = id ,_

  infixr 0 _⇒_
  field
    _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.⇒ Bˢ)
    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (S.app fˢ aˢ)
    app-[] :
      ∀ {Γ Δ A B} (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
      app f a [ γ ] ≡ᵗ[ S.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (S.lam bˢ)
    lam-[] :
      ∀ {Γ Δ A B} (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
      lam b [ γ ] ≡ᵗ[ S.lam-[] _ _ ] lam (b [ γ ↑ ])

    ⇒-β :
      ∀ {Γ A B} (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
      app (lam b) a ≡ᵗ[ S.⇒-β _ _ ] b [ ⟨ a ⟩ ]
    ⇒-η :
      ∀ {Γ A B} (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ S.⇒-η _ ] f

    ⊥ : Ty S.⊥
    ⊥-rec : ∀ {Γ} {A : Ty Aˢ} → Tm Γ ⊥ tˢ → Tm Γ A (S.⊥-rec tˢ)
    ⊥-rec-[] :
      ∀ {Γ Δ} {A : Ty Aˢ} (t : Tm Γ ⊥ tˢ) (γ : Sub Δ Γ γˢ) →
      ⊥-rec {A = A} t [ γ ] ≡ᵗ[ S.⊥-rec-[] _ _ ] ⊥-rec (t [ γ ])

    Bool : Ty S.Bool
    true : {Γ : Con Γˢ} → Tm Γ Bool S.true
    true-[] : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → true [ γ ] ≡ᵗ[ S.true-[] _ ] true
    false : {Γ : Con Γˢ} → Tm Γ Bool S.false
    false-[] : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → false [ γ ] ≡ᵗ[ S.false-[] _ ] false

    Bool-rec :
      ∀ {Γ A} →
      Tm Γ A a₁ˢ → Tm Γ A a₂ˢ → Tm Γ Bool tˢ → Tm Γ A (S.Bool-rec a₁ˢ a₂ˢ tˢ)
    Bool-rec-[] :
      ∀ {Γ Δ A}
      (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) (t : Tm Γ Bool tˢ) (γ : Sub Δ Γ γˢ) →
      Bool-rec a₁ a₂ t [ γ ] ≡ᵗ[ S.Bool-rec-[] _ _ _ _ ]
      Bool-rec (a₁ [ γ ]) (a₂ [ γ ]) (t [ γ ])

    Bool-β₁ :
      ∀ {Γ A} (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) →
      Bool-rec a₁ a₂ true ≡ᵗ[ S.Bool-β₁ _ _ ] a₁
    Bool-β₂ :
      ∀ {Γ A} (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) →
      Bool-rec a₁ a₂ false ≡ᵗ[ S.Bool-β₂ _ _ ] a₂

  instance
    H-Level-Sub : ∀ {Δ Γ} → H-Level (Sub Δ Γ γˢ) (2 + n)
    H-Level-Sub = basic-instance 2 Sub-is-set

    H-Level-Tm : ∀ {Γ A} → H-Level (Tm Γ A aˢ) (2 + n)
    H-Level-Tm = basic-instance 2 Tm-is-set
