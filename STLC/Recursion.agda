open import STLC.Model

module STLC.Recursion (M : Model) where

import STLC.Syntax as S
private module M = Model M

private variable
  Γ Δ : S.Con
  A : S.Ty

Ty-rec : S.Ty → M.Ty
Ty-rec (A S.⇒ B) = Ty-rec A M.⇒ Ty-rec B
Ty-rec S.⊥ = M.⊥
Ty-rec S.Bool = M.Bool

Con-rec : S.Con → M.Con
Con-rec (Γ S.▸ A) = Con-rec Γ M.▸ Ty-rec A
Con-rec S.◆ = M.◆

Sub-rec : S.Sub Δ Γ → M.Sub (Con-rec Δ) (Con-rec Γ)
Tm-rec : S.Tm Γ A → M.Tm (Con-rec Γ) (Ty-rec A)

Sub-rec (S.Sub-is-set γ₁ γ₂ p q i j) =
  M.Sub-is-set _ _ (λ k → Sub-rec (p k)) (λ k → Sub-rec (q k)) i j
Sub-rec (γ S.∘ δ) = Sub-rec γ M.∘ Sub-rec δ
Sub-rec (S.assoc γ δ θ i) = M.assoc (Sub-rec γ) (Sub-rec δ) (Sub-rec θ) i

Sub-rec S.id = M.id
Sub-rec (S.idr γ i) = M.idr (Sub-rec γ) i
Sub-rec (S.idl γ i) = M.idl (Sub-rec γ) i

Sub-rec S.p = M.p
Sub-rec (γ S., a) = Sub-rec γ M., Tm-rec a
Sub-rec (S.,-∘ γ a δ i) = M.,-∘ (Sub-rec γ) (Tm-rec a) (Sub-rec δ) i

Sub-rec (S.▸-β₁ γ a i) = M.▸-β₁ (Sub-rec γ) (Tm-rec a) i
Sub-rec (S.▸-η i) = M.▸-η i

Sub-rec S.ε = M.ε
Sub-rec (S.ε-∘ γ i) = M.ε-∘ (Sub-rec γ) i
Sub-rec (S.◆-η i) = M.◆-η i

Tm-rec (S.Tm-is-set a₁ a₂ p q i j) =
  M.Tm-is-set _ _ (λ k → Tm-rec (p k)) (λ k → Tm-rec (q k)) i j
Tm-rec (a S.[ γ ]) = Tm-rec a M.[ Sub-rec γ ]
Tm-rec (S.[]-∘ a γ δ i) = M.[]-∘ (Tm-rec a) (Sub-rec γ) (Sub-rec δ) i
Tm-rec (S.[]-id a i) = M.[]-id (Tm-rec a) i

Tm-rec S.q = M.q
Tm-rec (S.▸-β₂ γ a i) = M.▸-β₂ (Sub-rec γ) (Tm-rec a) i

Tm-rec (S.app f a) = M.app (Tm-rec f) (Tm-rec a)
Tm-rec (S.app-[] f a γ i) = M.app-[] (Tm-rec f) (Tm-rec a) (Sub-rec γ) i

Tm-rec (S.lam a) = M.lam (Tm-rec a)
Tm-rec (S.lam-[] a γ i) = M.lam-[] (Tm-rec a) (Sub-rec γ) i

Tm-rec (S.⇒-β f a i) = M.⇒-β (Tm-rec f) (Tm-rec a) i
Tm-rec (S.⇒-η a i) = M.⇒-η (Tm-rec a) i

Tm-rec (S.⊥-rec t) = M.⊥-rec (Tm-rec t)
Tm-rec (S.⊥-rec-[] t γ i) = M.⊥-rec-[] (Tm-rec t) (Sub-rec γ) i

Tm-rec S.true = M.true
Tm-rec (S.true-[] γ i) = M.true-[] (Sub-rec γ) i

Tm-rec S.false = M.false
Tm-rec (S.false-[] γ i) = M.false-[] (Sub-rec γ) i

Tm-rec (S.Bool-rec a₁ a₂ t) = M.Bool-rec (Tm-rec a₁) (Tm-rec a₂) (Tm-rec t)
Tm-rec (S.Bool-rec-[] a₁ a₂ t γ i) =
  M.Bool-rec-[] (Tm-rec a₁) (Tm-rec a₂) (Tm-rec t) (Sub-rec γ) i

Tm-rec (S.Bool-β₁ a₁ a₂ i) = M.Bool-β₁ (Tm-rec a₁) (Tm-rec a₂) i
Tm-rec (S.Bool-β₂ a₁ a₂ i) = M.Bool-β₂ (Tm-rec a₁) (Tm-rec a₂) i
