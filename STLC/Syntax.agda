module STLC.Syntax where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.Reflection.Marker
open import Data.Nat
open import Data.Dec
open import Data.Id.Base

private variable n : Nat

infixr 0 _⇒_
data Ty : Type where
  _⇒_ : Ty → Ty → Ty
  ⊥ Bool : Ty

Discreteᵢ-Ty : Discreteᵢ Ty
Discreteᵢ-Ty (A₁ ⇒ B₁) (A₂ ⇒ B₂) with Discreteᵢ-Ty A₁ A₂ | Discreteᵢ-Ty B₁ B₂
... | no ¬A₁≡A₂ | _ = no λ where reflᵢ → ¬A₁≡A₂ reflᵢ
... | yes _ | no ¬B₁≡B₂ = no λ where reflᵢ → ¬B₁≡B₂ reflᵢ
... | yes reflᵢ | yes reflᵢ  = yes reflᵢ
Discreteᵢ-Ty (A₁ ⇒ B₁) ⊥ = no λ ()
Discreteᵢ-Ty (A₁ ⇒ B₁) Bool = no λ ()

Discreteᵢ-Ty ⊥ (A₂ ⇒ B₂) = no λ ()
Discreteᵢ-Ty ⊥ ⊥ = yes reflᵢ
Discreteᵢ-Ty ⊥ Bool = no λ ()

Discreteᵢ-Ty Bool (A₂ ⇒ B₂) = no λ ()
Discreteᵢ-Ty Bool ⊥ = no λ ()
Discreteᵢ-Ty Bool Bool = yes reflᵢ

Discrete-Ty : Discrete Ty
Discrete-Ty = Discreteᵢ→discrete Discreteᵢ-Ty

Ty-is-set : is-set Ty
Ty-is-set = Discrete→is-set Discrete-Ty

instance
  H-Level-Ty : H-Level Ty (2 + n)
  H-Level-Ty = basic-instance 2 Ty-is-set

infixl 4 _▸_
data Con : Type where
  _▸_ : Con → Ty → Con
  ◆ : Con

Discreteᵢ-Con : Discreteᵢ Con
Discreteᵢ-Con (Γ₁ ▸ A₁) (Γ₂ ▸ A₂) with Discreteᵢ-Con Γ₁ Γ₂ | Discreteᵢ-Ty A₁ A₂
... | no ¬Γ₁≡Γ₂ | _ = no λ where reflᵢ → ¬Γ₁≡Γ₂ reflᵢ
... | yes _ | no ¬A₁≡A₂ = no λ where reflᵢ → ¬A₁≡A₂ reflᵢ
... | yes reflᵢ | yes reflᵢ = yes reflᵢ
Discreteᵢ-Con (Γ₁ ▸ A₁) ◆ = no λ ()

Discreteᵢ-Con ◆ (Γ₂ ▸ A₂) = no λ ()
Discreteᵢ-Con ◆ ◆ = yes reflᵢ

Discrete-Con : Discrete Con
Discrete-Con = Discreteᵢ→discrete Discreteᵢ-Con

Con-is-set : is-set Con
Con-is-set = Discrete→is-set Discrete-Con

instance
  H-Level-Con : H-Level Con (2 + n)
  H-Level-Con = basic-instance 2 Con-is-set

private variable
  Γ Δ Θ Ξ : Con
  A B : Ty

data Sub : Con → Con → Type
data Tm : Con → Ty → Type

private
  infixl 40 _[_]′
  _[_]′ : Tm Γ A → Sub Δ Γ → Tm Δ A
  q′ : Tm (Γ ▸ A) A

infixl 4 _↑
_↑ : Sub Δ Γ → Sub (Δ ▸ A) (Γ ▸ A)
⟨_⟩ : Tm Γ A → Sub Γ (Γ ▸ A)

infixl 40 _∘_
infixl 4 _,_
data Sub where
  Sub-is-set : is-set (Sub Δ Γ)
  _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  assoc : (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) → γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ

  id : Sub Γ Γ
  idr : (γ : Sub Δ Γ) → γ ∘ id ≡ γ
  idl : (γ : Sub Δ Γ) → id ∘ γ ≡ γ

  p : Sub (Γ ▸ A) Γ
  _,_ : Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▸ A)
  ,-∘ :
    (γ : Sub Δ Γ) (a : Tm Δ A) (δ : Sub Θ Δ) → (γ , a) ∘ δ ≡ (γ ∘ δ , a [ δ ]′)

  ▸-β₁ : (γ : Sub Δ Γ) (a : Tm Δ A) → p ∘ (γ , a) ≡ γ
  ▸-η : (p , q′) ≡ id {Γ ▸ A}

  ε : Sub Γ ◆
  ε-∘ : (γ : Sub Δ Γ) → ε ∘ γ ≡ ε
  ◆-η : ε ≡ id

infixl 40 _[_]
data Tm where
  Tm-is-set : is-set (Tm Γ A)
  _[_] : Tm Γ A → Sub Δ Γ → Tm Δ A
  []-∘ : (a : Tm Γ A) (γ : Sub Δ Γ) (δ : Sub Θ Δ) → a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
  []-id : (a : Tm Γ A) → a [ id ] ≡ a

  q : Tm (Γ ▸ A) A
  ▸-β₂ : (γ : Sub Δ Γ) (a : Tm Δ A) → q [ γ , a ] ≡ a

  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  app-[] :
    ∀ (f : Tm Γ (A ⇒ B)) a (γ : Sub Δ Γ) →
    app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

  lam : Tm (Γ ▸ A) B → Tm Γ (A ⇒ B)
  lam-[] : (b : Tm (Γ ▸ A) B) (γ : Sub Δ Γ) → lam b [ γ ] ≡ lam (b [ γ ↑ ])

  ⇒-β : ∀ (b : Tm (Γ ▸ A) B) a → app (lam b) a ≡ b [ ⟨ a ⟩ ]
  ⇒-η : (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

  ⊥-rec : Tm Γ ⊥ → Tm Γ A
  ⊥-rec-[] : ∀ t (γ : Sub Δ Γ) → ⊥-rec {A = A} t [ γ ] ≡ ⊥-rec (t [ γ ])

  true : Tm Γ Bool
  true-[] : (γ : Sub Δ Γ) → true [ γ ] ≡ true

  false : Tm Γ Bool
  false-[] : (γ : Sub Δ Γ) → false [ γ ] ≡ false

  Bool-rec : Tm Γ A → Tm Γ A → Tm Γ Bool → Tm Γ A
  Bool-rec-[] :
    ∀ (a₁ a₂ : Tm Γ A) t (γ : Sub Δ Γ) →
    Bool-rec a₁ a₂ t [ γ ] ≡ Bool-rec (a₁ [ γ ]) (a₂ [ γ ]) (t [ γ ])

  Bool-β₁ : (a₁ a₂ : Tm Γ A) → Bool-rec a₁ a₂ true ≡ a₁
  Bool-β₂ : (a₁ a₂ : Tm Γ A) → Bool-rec a₁ a₂ false ≡ a₂

_[_]′ = _[_]
q′ = q
γ ↑ = γ ∘ p , q
⟨_⟩ = id ,_

instance
  H-Level-Sub : H-Level (Sub Δ Γ) (2 + n)
  H-Level-Sub = basic-instance 2 Sub-is-set

  H-Level-Tm : H-Level (Tm Γ A) (2 + n)
  H-Level-Tm = basic-instance 2 Tm-is-set

↑-∘ :
  (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
  Path (Sub (Θ ▸ A) (Γ ▸ A)) (γ ∘ δ ↑) ((γ ↑) ∘ (δ ↑))
↑-∘ γ δ =
  ⌜ γ ∘ δ ∘ p ⌝ , q         ≡˘⟨ ap¡ (assoc _ _ _) ⟩
  γ ∘ ⌜ δ ∘ p ⌝ , q         ≡˘⟨ ap¡ (▸-β₁ _ _) ⟩
  ⌜ γ ∘ (p ∘ (δ ↑)) ⌝ , q   ≡⟨ ap! (assoc _ _ _) ⟩
  γ ∘ p ∘ (δ ↑) , ⌜ q ⌝     ≡˘⟨ ap¡ (▸-β₂ _ _) ⟩
  γ ∘ p ∘ (δ ↑) , q [ δ ↑ ] ≡˘⟨ ,-∘ _ _ _ ⟩
  (γ ↑) ∘ (δ ↑)             ∎

↑-id : (id ↑) ≡ id {Γ ▸ A}
↑-id =
  ⌜ id ∘ p ⌝ , q ≡⟨ ap! (idl _) ⟩
  p , q          ≡⟨ ▸-η ⟩
  id             ∎

↑-⟨⟩ : (γ : Sub Δ Γ) (a : Tm Δ A) → (γ ↑) ∘ ⟨ a ⟩ ≡ (γ , a)
↑-⟨⟩ γ a =
  (γ ↑) ∘ ⟨ a ⟩                   ≡⟨ ,-∘ _ _ _ ⟩
  ⌜ γ ∘ p ∘ ⟨ a ⟩ ⌝ , q [ ⟨ a ⟩ ] ≡˘⟨ ap¡ (assoc _ _ _) ⟩
  γ ∘ ⌜ p ∘ ⟨ a ⟩ ⌝ , q [ ⟨ a ⟩ ] ≡⟨ ap! (▸-β₁ _ _) ⟩
  ⌜ γ ∘ id ⌝ , q [ ⟨ a ⟩ ]        ≡⟨ ap! (idr _) ⟩
  γ , ⌜ q [ ⟨ a ⟩ ] ⌝             ≡⟨ ap! (▸-β₂ _ _) ⟩
  γ , a                           ∎
