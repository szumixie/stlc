module STLC.Weakening where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.Equiv
open import 1Lab.Univalence
open import 1Lab.Reflection.Marker
open import Data.Dec
open import Data.Id.Base
open import Data.Nat
import 1Lab.Prelude as P
import STLC.Syntax as S

private variable
  n : Nat
  Γ Δ Θ Ξ : S.Con
  A A₁ A₂ B : S.Ty

infixl 4 _↑ _∘p
data Wk : S.Con → S.Con → Type where
  ε : Wk S.◆ S.◆
  _∘p : Wk Δ Γ → Wk (Δ S.▸ A) Γ
  _↑ : Wk Δ Γ → Wk (Δ S.▸ A) (Γ S.▸ A)

Discreteᵢ-Wk : Discreteᵢ (Wk Δ Γ)
Discreteᵢ-Wk = subst Discreteᵢ (ua Wk′≃Wk) Discreteᵢ-Wk′
  where
  infixl 4 _∘p _↑⟨_⟩
  data Wk′ : S.Con → S.Con → Type where
    ε : Wk′ S.◆ S.◆
    _∘p : Wk′ Δ Γ → Wk′ (Δ S.▸ A) Γ
    _↑⟨_⟩ : Wk′ Δ Γ → A₁ ≡ᵢ A₂ → Wk′ (Δ S.▸ A₁) (Γ S.▸ A₂)

  Wk′≃Wk : Wk′ Δ Γ ≃ Wk Δ Γ
  Wk′≃Wk = Iso→Equiv (fun P., iso inv invr invl)
    where
    fun : Wk′ Δ Γ → Wk Δ Γ
    fun ε = ε
    fun (γ ∘p) = fun γ ∘p
    fun (γ ↑⟨ reflᵢ ⟩) = fun γ ↑

    inv : Wk Δ Γ → Wk′ Δ Γ
    inv ε = ε
    inv (γ ∘p) = inv γ ∘p
    inv (γ ↑) = inv γ ↑⟨ reflᵢ ⟩

    invr : is-right-inverse inv (fun {Δ} {Γ})
    invr ε = refl
    invr (γ ∘p) = ap _∘p (invr γ)
    invr (γ ↑) = ap _↑ (invr γ)

    invl : is-left-inverse inv (fun {Δ} {Γ})
    invl ε = refl
    invl (γ ∘p) = ap _∘p (invl γ)
    invl (γ ↑⟨ reflᵢ ⟩) = ap _↑⟨ reflᵢ ⟩ (invl γ)

  Discreteᵢ-Wk′ : Discreteᵢ (Wk′ Δ Γ)
  Discreteᵢ-Wk′ ε ε = yes reflᵢ
  Discreteᵢ-Wk′ (γ₁ ∘p) (γ₂ ∘p) with Discreteᵢ-Wk′ γ₁ γ₂
  ... | no ¬γ₁≡γ₂ = no λ where reflᵢ → ¬γ₁≡γ₂ reflᵢ
  ... | yes reflᵢ = yes reflᵢ
  Discreteᵢ-Wk′ (γ₁ ∘p) (γ₂ ↑⟨ p₂ ⟩) = no λ ()

  Discreteᵢ-Wk′ (γ₁ ↑⟨ p₁ ⟩) (γ₂ ∘p) = no λ ()
  Discreteᵢ-Wk′ (γ₁ ↑⟨ p₁ ⟩) (γ₂ ↑⟨ p₂ ⟩)with Discreteᵢ-Wk′ γ₁ γ₂
  ... | no ¬γ₁≡γ₂ = no λ where reflᵢ → ¬γ₁≡γ₂ reflᵢ
  ... | yes reflᵢ =
    yes (Id≃path.from (ap (γ₁ ↑⟨_⟩) (is-set→is-setᵢ S.Ty-is-set _ _ p₁ p₂)))

Discrete-Wk : Discrete (Wk Δ Γ)
Discrete-Wk = Discreteᵢ→discrete Discreteᵢ-Wk

Wk-is-set : is-set (Wk Δ Γ)
Wk-is-set = Discrete→is-set Discrete-Wk

instance
  H-Level-Wk : H-Level (Wk Δ Γ) (2 + n)
  H-Level-Wk = basic-instance 2 Wk-is-set

Wk-emb : Wk Δ Γ → S.Sub Δ Γ
Wk-emb ε = S.ε
Wk-emb (γ ∘p) = Wk-emb γ S.∘ S.p
Wk-emb (γ ↑) = Wk-emb γ S.↑

infixl 40 _∘_
_∘_ : Wk Δ Γ → Wk Θ Δ → Wk Θ Γ
γ ∘ ε = γ
γ ∘ (δ ∘p) = γ ∘ δ ∘p
(γ ∘p) ∘ (δ ↑) = γ ∘ δ ∘p
(γ ↑) ∘ (δ ↑) = γ ∘ δ ↑

Wk-emb-∘ : (γ : Wk Δ Γ) (δ : Wk Θ Δ) → Wk-emb (γ ∘ δ) ≡ Wk-emb γ S.∘ Wk-emb δ
Wk-emb-∘ γ ε =
  Wk-emb γ              ≡˘⟨ S.idr _ ⟩
  Wk-emb γ S.∘ ⌜ S.id ⌝ ≡˘⟨ ap¡ S.◆-η ⟩
  Wk-emb γ S.∘ S.ε      ∎
Wk-emb-∘ γ (δ ∘p) =
  ⌜ Wk-emb (γ ∘ δ) ⌝ S.∘ S.p      ≡⟨ ap! (Wk-emb-∘ _ _) ⟩
  Wk-emb γ S.∘ Wk-emb δ S.∘ S.p   ≡˘⟨ S.assoc _ _ _ ⟩
  Wk-emb γ S.∘ (Wk-emb δ S.∘ S.p) ∎
Wk-emb-∘ (γ ∘p) (δ ↑) =
  ⌜ Wk-emb (γ ∘ δ) ⌝ S.∘ S.p            ≡⟨ ap! (Wk-emb-∘ _ _) ⟩
  Wk-emb γ S.∘ Wk-emb δ S.∘ S.p         ≡˘⟨ S.assoc _ _ _ ⟩
  Wk-emb γ S.∘ ⌜ Wk-emb δ S.∘ S.p ⌝     ≡˘⟨ ap¡ (S.▸-β₁ _ _) ⟩
  Wk-emb γ S.∘ (S.p S.∘ (Wk-emb δ S.↑)) ≡⟨ S.assoc _ _ _ ⟩
  Wk-emb γ S.∘ S.p S.∘ (Wk-emb δ S.↑)   ∎
Wk-emb-∘ (γ ↑) (δ ↑) =
  ⌜ Wk-emb (γ ∘ δ) ⌝ S.↑            ≡⟨ ap! (Wk-emb-∘ _ _) ⟩
  Wk-emb γ S.∘ Wk-emb δ S.↑         ≡⟨ S.↑-∘ _ _ ⟩
  (Wk-emb γ S.↑) S.∘ (Wk-emb δ S.↑) ∎

assoc : (γ : Wk Δ Γ) (δ : Wk Θ Δ) (θ : Wk Ξ Θ) → γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ
assoc γ δ ε = refl
assoc γ δ (θ ∘p) = ap _∘p (assoc γ δ θ)
assoc γ (δ ∘p) (θ ↑) = ap _∘p (assoc γ δ θ)
assoc (γ ∘p) (δ ↑) (θ ↑) = ap _∘p (assoc γ δ θ)
assoc (γ ↑) (δ ↑) (θ ↑) = ap _↑ (assoc γ δ θ)

id : Wk Γ Γ
id {Γ S.▸ A} = id ↑
id {S.◆} = ε

Wk-emb-id : Wk-emb id ≡ S.id {Γ}
Wk-emb-id {Γ S.▸ A} =
  ⌜ Wk-emb id ⌝ S.↑ ≡⟨ ap! Wk-emb-id ⟩
  S.id S.↑          ≡⟨ S.↑-id ⟩
  S.id              ∎
Wk-emb-id {S.◆} = S.◆-η

idr : (γ : Wk Δ Γ) → γ ∘ id ≡ γ
idr ε = refl
idr (γ ∘p) = ap _∘p (idr _)
idr (γ ↑) = ap _↑ (idr _)

idl : (γ : Wk Δ Γ) → id ∘ γ ≡ γ
idl ε = refl
idl (γ ∘p) = ap _∘p (idl _)
idl (γ ↑) = ap _↑ (idl _)

infixl 4 _[p]
data Var : S.Con → S.Ty → Type where
  q : Var (Γ S.▸ A) A
  _[p] : Var Γ A → Var (Γ S.▸ B) A

Discreteᵢ-Var : Discreteᵢ (Var Γ A)
Discreteᵢ-Var = subst Discreteᵢ (ua Var′≃Var) Discreteᵢ-Var′
  where
  infixl 4 _[p]
  data Var′ : S.Con → S.Ty → Type where
    q⟨_⟩ : ∀ {A₁ A₂} → A₁ ≡ᵢ A₂ → Var′ (Γ S.▸ A₁) A₂
    _[p] : Var′ Γ A → Var′ (Γ S.▸ B) A

  Var′≃Var : Var′ Γ A ≃ Var Γ A
  Var′≃Var = Iso→Equiv (fun P., iso inv invr invl)
    where
    fun : Var′ Γ A → Var Γ A
    fun q⟨ reflᵢ ⟩ = q
    fun (a [p]) = fun a [p]

    inv : Var Γ A → Var′ Γ A
    inv q = q⟨ reflᵢ ⟩
    inv (a [p]) = inv a [p]

    invr : is-right-inverse inv (fun {Γ} {A})
    invr q = refl
    invr (a [p]) = ap _[p] (invr a)

    invl : is-left-inverse inv (fun {Γ} {A})
    invl q⟨ reflᵢ ⟩ = refl
    invl (a [p]) = ap _[p] (invl a)

  Discreteᵢ-Var′ : Discreteᵢ (Var′ Γ A)
  Discreteᵢ-Var′ q⟨ p₁ ⟩ q⟨ p₂ ⟩ =
    yes (Id≃path.from (ap q⟨_⟩ (is-set→is-setᵢ S.Ty-is-set _ _ p₁ p₂)))
  Discreteᵢ-Var′ q⟨ p₁ ⟩ (a₂ [p]) = no λ ()

  Discreteᵢ-Var′ (a₁ [p]) q⟨ p₂ ⟩ = no λ ()
  Discreteᵢ-Var′ (a₁ [p]) (a₂ [p]) with Discreteᵢ-Var′ a₁ a₂
  ... | yes reflᵢ = yes reflᵢ
  ... | no ¬a₁≡a₂ = no λ where reflᵢ → ¬a₁≡a₂ reflᵢ

Discrete-Var : Discrete (Var Γ A)
Discrete-Var = Discreteᵢ→discrete Discreteᵢ-Var

Var-is-set : is-set (Var Γ A)
Var-is-set = Discrete→is-set Discrete-Var

instance
  H-Level-Var : H-Level (Var Γ A) (2 + n)
  H-Level-Var = basic-instance 2 Var-is-set

Var-emb : Var Γ A → S.Tm Γ A
Var-emb q = S.q
Var-emb (a [p]) = Var-emb a S.[ S.p ]

infixl 40 _[_]
_[_] : Var Γ A → Wk Δ Γ → Var Δ A
a [ ε ] = a
a [ γ ∘p ] = a [ γ ] [p]
q [ γ ↑ ] = q
(a [p]) [ γ ↑ ] = a [ γ ] [p]

Var-emb-[] :
  (a : Var Γ A) (γ : Wk Δ Γ) → Var-emb (a [ γ ]) ≡ Var-emb a S.[ Wk-emb γ ]
Var-emb-[] a (γ ∘p) =
  ⌜ Var-emb (a [ γ ]) ⌝ S.[ S.p ]    ≡⟨ ap! (Var-emb-[] _ _) ⟩
  Var-emb a S.[ Wk-emb γ ] S.[ S.p ] ≡˘⟨ S.[]-∘ _ _ _ ⟩
  Var-emb a S.[ Wk-emb γ S.∘ S.p ]   ∎
Var-emb-[] q (γ ↑) = sym (S.▸-β₂ _ _)
Var-emb-[] (a [p]) (γ ↑) =
  ⌜ Var-emb (a [ γ ]) ⌝ S.[ S.p ]        ≡⟨ ap! (Var-emb-[] _ _) ⟩
  Var-emb a S.[ Wk-emb γ ] S.[ S.p ]     ≡˘⟨ S.[]-∘ _ _ _ ⟩
  Var-emb a S.[ ⌜ Wk-emb γ S.∘ S.p ⌝ ]   ≡˘⟨ ap¡ (S.▸-β₁ _ _) ⟩
  Var-emb a S.[ S.p S.∘ (Wk-emb γ S.↑) ] ≡⟨ S.[]-∘ _ _ _ ⟩
  Var-emb a S.[ S.p ] S.[ Wk-emb γ S.↑ ] ∎

[]-∘ : (a : Var Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
[]-∘ a γ ε = refl
[]-∘ a γ (δ ∘p) = ap _[p] ([]-∘ a γ δ)
[]-∘ a (γ ∘p) (δ ↑) = ap _[p] ([]-∘ a γ δ)
[]-∘ q (γ ↑) (δ ↑) = refl
[]-∘ (a [p]) (γ ↑) (δ ↑) = ap _[p] ([]-∘ a γ δ)

[]-id : (a : Var Γ A) → a [ id ] ≡ a
[]-id q = refl
[]-id (a [p]) = ap _[p] ([]-id _)
