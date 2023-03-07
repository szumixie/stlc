module STLC.NormalForm where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.Reflection.Marker
open import Data.Dec
open import Data.Id.Base
open import Data.Nat
import STLC.Syntax as S
open import STLC.Weakening

private variable
  n : Nat
  Γ Δ Θ : S.Con
  A B : S.Ty

data Ne : S.Con → S.Ty → Type
data Nf : S.Con → S.Ty → Type

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (A S.⇒ B) → Nf Γ A → Ne Γ B
  ⊥-rec : Ne Γ S.⊥ → Ne Γ A
  Bool-rec : Nf Γ A → Nf Γ A → Ne Γ S.Bool → Ne Γ A

data Nf where
  lam : Nf (Γ S.▸ A) B → Nf Γ (A S.⇒ B)
  ⊥-ne : Ne Γ S.⊥ → Nf Γ S.⊥
  Bool-ne : Ne Γ S.Bool → Nf Γ S.Bool
  true false : Nf Γ S.Bool

Discreteᵢ-Ne : Discreteᵢ (Ne Γ A)
Discreteᵢ-Nf : Discreteᵢ (Nf Γ A)

Discreteᵢ-Ne (var a₁) (var a₂) with Discreteᵢ-Var a₁ a₂
... | no ¬a₁≡a₂ = no λ where reflᵢ → ¬a₁≡a₂ reflᵢ
... | yes reflᵢ = yes reflᵢ
Discreteᵢ-Ne (var a₁) (app f₂ a₂) = no λ ()
Discreteᵢ-Ne (var a₁) (⊥-rec t₂) = no λ ()
Discreteᵢ-Ne (var a₁) (Bool-rec a₁₂ a₂₂ t₂) = no λ ()

Discreteᵢ-Ne (app f₁ a₁) (var a₂) = no λ ()
Discreteᵢ-Ne {Γ} {B} (app {A = A₁} f₁ a₁) (app {A = A₂} f₂ a₂) with S.Discreteᵢ-Ty A₁ A₂
... | no ¬A₁≡A₂ = no λ where reflᵢ → ¬A₁≡A₂ reflᵢ
... | yes reflᵢ with Discreteᵢ-Ne f₁ f₂ | Discreteᵢ-Nf a₁ a₂
... | no ¬f₁≡f₂ | _ = no λ p → ¬f₁≡f₂ (app-inj₁ reflᵢ p)
  where
  app-inj₁ :
    ∀ {A₂} {f₂ : Ne Γ (A₂ S.⇒ B)} {a₂ : Nf Γ A₂} (A₁≡A₂ : A₁ ≡ᵢ A₂) →
    app f₁ a₁ ≡ᵢ app f₂ a₂ → substᵢ (λ A → Ne Γ (A S.⇒ B)) A₁≡A₂ f₁ ≡ᵢ f₂
  app-inj₁ A₁≡A₂ reflᵢ =
    subst
      (λ A₁≡A₂ → substᵢ (λ A → Ne Γ (A S.⇒ B)) A₁≡A₂ f₁ ≡ᵢ f₁)
      (is-set→is-setᵢ S.Ty-is-set _ _ reflᵢ A₁≡A₂)
      reflᵢ
... | yes _ | no ¬a₁≡a₂ = no λ p → ¬a₁≡a₂ (app-inj₂ reflᵢ p)
  where
  app-inj₂ :
    ∀ {A₂} {f₂ : Ne Γ (A₂ S.⇒ B)} {a₂ : Nf Γ A₂} (A₁≡A₂ : A₁ ≡ᵢ A₂) →
    app f₁ a₁ ≡ᵢ app f₂ a₂ → substᵢ (Nf Γ) A₁≡A₂ a₁ ≡ᵢ a₂
  app-inj₂ A₁≡A₂ reflᵢ =
    subst
      (λ A₁≡A₂ → substᵢ (Nf Γ) A₁≡A₂ a₁ ≡ᵢ a₁)
      (is-set→is-setᵢ S.Ty-is-set _ _ reflᵢ A₁≡A₂)
      reflᵢ
... | yes reflᵢ | yes reflᵢ = yes reflᵢ
Discreteᵢ-Ne (app f₁ a₁) (⊥-rec t₂) = no λ ()
Discreteᵢ-Ne (app f₁ a₁) (Bool-rec a₁₂ a₂₂ t₂) = no λ ()

Discreteᵢ-Ne (⊥-rec t₁) (var a₂) = no λ ()
Discreteᵢ-Ne (⊥-rec t₁) (app f₂ a₂) = no λ ()
Discreteᵢ-Ne (⊥-rec t₁) (⊥-rec t₂) with Discreteᵢ-Ne t₁ t₂
... | no ¬t₁≡t₂ = no λ where reflᵢ → ¬t₁≡t₂ reflᵢ
... | yes reflᵢ = yes reflᵢ
Discreteᵢ-Ne (⊥-rec t₁) (Bool-rec a₁₂ a₂₂ t₂) = no λ ()

Discreteᵢ-Ne (Bool-rec a₁₁ a₂₁ t₁) (var a₂) = no λ ()
Discreteᵢ-Ne (Bool-rec a₁₁ a₂₁ t₁) (app t₂ a₂) = no λ ()
Discreteᵢ-Ne (Bool-rec a₁₁ a₂₁ t₁) (⊥-rec t₂) = no λ ()
Discreteᵢ-Ne (Bool-rec a₁₁ a₂₁ t₁) (Bool-rec a₁₂ a₂₂ t₂)
  with Discreteᵢ-Nf a₁₁ a₁₂ | Discreteᵢ-Nf a₂₁ a₂₂ | Discreteᵢ-Ne t₁ t₂
... | no ¬a₁₁≡a₁₂ | _ | _ = no λ where reflᵢ → ¬a₁₁≡a₁₂ reflᵢ
... | yes _ | no ¬a₂₁≡a₂₂ | _ = no λ where reflᵢ → ¬a₂₁≡a₂₂ reflᵢ
... | yes _ | yes _ | no ¬t₁≡t₂ = no λ where reflᵢ → ¬t₁≡t₂ reflᵢ
... | yes reflᵢ | yes reflᵢ | yes reflᵢ = yes reflᵢ

Discreteᵢ-Nf (lam b₁) (lam b₂) with Discreteᵢ-Nf b₁ b₂
... | no ¬b₁≡b₂ = no λ where reflᵢ → ¬b₁≡b₂ reflᵢ
... | yes reflᵢ = yes reflᵢ
Discreteᵢ-Nf (⊥-ne t₁) (⊥-ne t₂) with Discreteᵢ-Ne t₁ t₂
... | no ¬t₁≡t₂ = no λ where reflᵢ → ¬t₁≡t₂ reflᵢ
... | yes reflᵢ = yes reflᵢ

Discreteᵢ-Nf (Bool-ne t₁) (Bool-ne t₂) with Discreteᵢ-Ne t₁ t₂
... | no ¬t₁≡t₂ = no λ where reflᵢ → ¬t₁≡t₂ reflᵢ
... | yes reflᵢ = yes reflᵢ
Discreteᵢ-Nf (Bool-ne t₁) true = no λ ()
Discreteᵢ-Nf (Bool-ne t₁) false = no λ ()

Discreteᵢ-Nf true (Bool-ne t₂) = no λ ()
Discreteᵢ-Nf true true = yes reflᵢ
Discreteᵢ-Nf true false = no λ ()

Discreteᵢ-Nf false (Bool-ne t₂) = no λ ()
Discreteᵢ-Nf false true = no λ ()
Discreteᵢ-Nf false false = yes reflᵢ

Discrete-Ne : Discrete (Ne Γ A)
Discrete-Ne = Discreteᵢ→discrete Discreteᵢ-Ne

Discrete-Nf : Discrete (Nf Γ A)
Discrete-Nf = Discreteᵢ→discrete Discreteᵢ-Nf

Ne-is-set : is-set (Ne Γ A)
Ne-is-set = Discrete→is-set Discrete-Ne

Nf-is-set : is-set (Nf Γ A)
Nf-is-set = Discrete→is-set Discrete-Nf

instance
  H-Level-Ne : H-Level (Ne Γ A) (2 + n)
  H-Level-Ne = basic-instance 2 Ne-is-set

  H-Level-Nf : H-Level (Nf Γ A) (2 + n)
  H-Level-Nf = basic-instance 2 Nf-is-set

Ne-emb : Ne Γ A → S.Tm Γ A
Nf-emb : Nf Γ A → S.Tm Γ A

Ne-emb (var a) = Var-emb a
Ne-emb (app f a) = S.app (Ne-emb f) (Nf-emb a)
Ne-emb (⊥-rec t) = S.⊥-rec (Ne-emb t)
Ne-emb (Bool-rec a₁ a₂ t) = S.Bool-rec (Nf-emb a₁) (Nf-emb a₂) (Ne-emb t)

Nf-emb (lam a) = S.lam (Nf-emb a)
Nf-emb (⊥-ne t) = Ne-emb t
Nf-emb (Bool-ne t) = Ne-emb t
Nf-emb true = S.true
Nf-emb false = S.false

infixl 40 _[_]ᴺᵉ _[_]ᴺᶠ
_[_]ᴺᵉ : Ne Γ A → Wk Δ Γ → Ne Δ A
_[_]ᴺᶠ : Nf Γ A → Wk Δ Γ → Nf Δ A

var a [ γ ]ᴺᵉ = var (a [ γ ])
app f a [ γ ]ᴺᵉ = app (f [ γ ]ᴺᵉ) (a [ γ ]ᴺᶠ)
⊥-rec t [ γ ]ᴺᵉ = ⊥-rec (t [ γ ]ᴺᵉ)
Bool-rec a₁ a₂ t [ γ ]ᴺᵉ = Bool-rec (a₁ [ γ ]ᴺᶠ) (a₂ [ γ ]ᴺᶠ) (t [ γ ]ᴺᵉ)

lam b [ γ ]ᴺᶠ = lam (b [ γ ↑ ]ᴺᶠ)
⊥-ne t [ γ ]ᴺᶠ = ⊥-ne (t [ γ ]ᴺᵉ)
Bool-ne t [ γ ]ᴺᶠ = Bool-ne (t [ γ ]ᴺᵉ)
true [ γ ]ᴺᶠ = true
false [ γ ]ᴺᶠ = false

Ne-emb-[] :
  (a : Ne Γ A) (γ : Wk Δ Γ) → Ne-emb (a [ γ ]ᴺᵉ) ≡ Ne-emb a S.[ Wk-emb γ ]
Nf-emb-[] :
  (a : Nf Γ A) (γ : Wk Δ Γ) → Nf-emb (a [ γ ]ᴺᶠ) ≡ Nf-emb a S.[ Wk-emb γ ]

Ne-emb-[] (var a) γ = Var-emb-[] _ _
Ne-emb-[] (app f a) γ =
  S.app ⌜ Ne-emb (f [ γ ]ᴺᵉ) ⌝ (Nf-emb (a [ γ ]ᴺᶠ))         ≡⟨ ap! (Ne-emb-[] f _) ⟩
  S.app (Ne-emb f S.[ Wk-emb γ ]) ⌜ Nf-emb (a [ γ ]ᴺᶠ) ⌝    ≡⟨ ap! (Nf-emb-[] a _) ⟩
  S.app (Ne-emb f S.[ Wk-emb γ ]) (Nf-emb a S.[ Wk-emb γ ]) ≡˘⟨ S.app-[] _ _ _ ⟩
  S.app (Ne-emb f) (Nf-emb a) S.[ Wk-emb γ ]                ∎
Ne-emb-[] (⊥-rec t) γ =
  S.⊥-rec ⌜ Ne-emb (t [ γ ]ᴺᵉ) ⌝    ≡⟨ ap! (Ne-emb-[] t _) ⟩
  S.⊥-rec (Ne-emb t S.[ Wk-emb γ ]) ≡˘⟨ S.⊥-rec-[] _ _ ⟩
  S.⊥-rec (Ne-emb t) S.[ Wk-emb γ ] ∎
Ne-emb-[] (Bool-rec a₁ a₂ t) γ =
  S.Bool-rec ⌜ Nf-emb (a₁ [ γ ]ᴺᶠ) ⌝ (Nf-emb (a₂ [ γ ]ᴺᶠ)) (Ne-emb (t [ γ ]ᴺᵉ))              ≡⟨ ap! (Nf-emb-[] a₁ _) ⟩
  S.Bool-rec (Nf-emb a₁ S.[ Wk-emb γ ]) ⌜ Nf-emb (a₂ [ γ ]ᴺᶠ) ⌝ (Ne-emb (t [ γ ]ᴺᵉ))         ≡⟨ ap! (Nf-emb-[] a₂ _) ⟩
  S.Bool-rec (Nf-emb a₁ S.[ Wk-emb γ ]) (Nf-emb a₂ S.[ Wk-emb γ ]) ⌜ Ne-emb (t [ γ ]ᴺᵉ) ⌝    ≡⟨ ap! (Ne-emb-[] t _) ⟩
  S.Bool-rec (Nf-emb a₁ S.[ Wk-emb γ ]) (Nf-emb a₂ S.[ Wk-emb γ ]) (Ne-emb t S.[ Wk-emb γ ]) ≡˘⟨ S.Bool-rec-[] _ _ _ _ ⟩
  S.Bool-rec (Nf-emb a₁) (Nf-emb a₂) (Ne-emb t) S.[ Wk-emb γ ]                               ∎

Nf-emb-[] (lam b) γ =
  S.lam ⌜ Nf-emb (b [ γ ↑ ]ᴺᶠ) ⌝      ≡⟨ ap! (Nf-emb-[] b _) ⟩
  S.lam (Nf-emb b S.[ Wk-emb γ S.↑ ]) ≡˘⟨ S.lam-[] _ _ ⟩
  S.lam (Nf-emb b) S.[ Wk-emb γ ]     ∎
Nf-emb-[] (⊥-ne t) γ = Ne-emb-[] t γ
Nf-emb-[] (Bool-ne t) γ = Ne-emb-[] t γ
Nf-emb-[] true γ = sym (S.true-[] _)
Nf-emb-[] false γ = sym (S.false-[] _)

[]ᴺᵉ-∘ :
  (a : Ne Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘ δ ]ᴺᵉ ≡ a [ γ ]ᴺᵉ [ δ ]ᴺᵉ
[]ᴺᶠ-∘ :
  (a : Nf Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘ δ ]ᴺᶠ ≡ a [ γ ]ᴺᶠ [ δ ]ᴺᶠ

[]ᴺᵉ-∘ (var a) γ δ = ap var ([]-∘ a γ δ)
[]ᴺᵉ-∘ (app f a) γ δ = ap₂ app ([]ᴺᵉ-∘ _ _ _) ([]ᴺᶠ-∘ _ _ _)
[]ᴺᵉ-∘ (⊥-rec t) γ δ = ap ⊥-rec ([]ᴺᵉ-∘ _ _ _)
[]ᴺᵉ-∘ (Bool-rec a₁ a₂ t) γ δ = λ i →
  Bool-rec ([]ᴺᶠ-∘ a₁ γ δ i) ([]ᴺᶠ-∘ a₂ γ δ i) ([]ᴺᵉ-∘ t γ δ i)

[]ᴺᶠ-∘ (lam b) γ δ = ap lam ([]ᴺᶠ-∘ _ _ _)
[]ᴺᶠ-∘ (⊥-ne t) γ δ = ap ⊥-ne ([]ᴺᵉ-∘ _ _ _)
[]ᴺᶠ-∘ (Bool-ne t) γ δ = ap Bool-ne ([]ᴺᵉ-∘ _ _ _)
[]ᴺᶠ-∘ true γ δ = refl
[]ᴺᶠ-∘ false γ δ = refl

[]ᴺᵉ-id : (a : Ne Γ A) → a [ id ]ᴺᵉ ≡ a
[]ᴺᶠ-id : (a : Nf Γ A) → a [ id ]ᴺᶠ ≡ a

[]ᴺᵉ-id (var a) = ap var ([]-id _)
[]ᴺᵉ-id (app f a) = ap₂ app ([]ᴺᵉ-id _) ([]ᴺᶠ-id _)
[]ᴺᵉ-id (⊥-rec t) = ap ⊥-rec ([]ᴺᵉ-id _)
[]ᴺᵉ-id (Bool-rec a₁ a₂ t) = λ i →
  Bool-rec ([]ᴺᶠ-id a₁ i) ([]ᴺᶠ-id a₂ i) ([]ᴺᵉ-id t i)

[]ᴺᶠ-id (lam b) = ap lam ([]ᴺᶠ-id _)
[]ᴺᶠ-id (⊥-ne t) = ap ⊥-ne ([]ᴺᵉ-id _)
[]ᴺᶠ-id (Bool-ne t) = ap Bool-ne ([]ᴺᵉ-id _)
[]ᴺᶠ-id true = refl
[]ᴺᶠ-id false = refl
