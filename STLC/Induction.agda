open import STLC.Displayed

module STLC.Induction (M : Displayed) where

open import 1Lab.Prelude
import STLC.Syntax as S
private module M = Displayed M

private variable
  Γ Δ : S.Con
  A : S.Ty

Ty-ind : ∀ A → M.Ty A
Ty-ind (A S.⇒ B) = Ty-ind A M.⇒ Ty-ind B
Ty-ind S.⊥ = M.⊥
Ty-ind S.Bool = M.Bool

Con-ind : ∀ Γ → M.Con Γ
Con-ind (Γ S.▸ A) = Con-ind Γ M.▸ Ty-ind A
Con-ind S.◆ = M.◆

Sub-ind : ∀ γ → M.Sub (Con-ind Δ) (Con-ind Γ) γ
Tm-ind : ∀ a → M.Tm (Con-ind Γ) (Ty-ind A) a

Sub-ind (S.Sub-is-set γ₁ γ₂ p q i j) =
  is-set→squarep
    {A = λ i j → M.Sub _ _ (S.Sub-is-set _ _ _ _ i j)}
    (λ i j → hlevel 2) refl (λ j → Sub-ind (p j)) (λ j → Sub-ind (q j)) refl i j
Sub-ind (γ S.∘ δ) = Sub-ind γ M.∘ Sub-ind δ
Sub-ind (S.assoc γ δ θ i) = M.assoc (Sub-ind γ) (Sub-ind δ) (Sub-ind θ) i

Sub-ind S.id = M.id
Sub-ind (S.idr γ i) = M.idr (Sub-ind γ) i
Sub-ind (S.idl γ i) = M.idl (Sub-ind γ) i

Sub-ind S.p = M.p
Sub-ind (γ S., a) = Sub-ind γ M., Tm-ind a
Sub-ind (S.,-∘ γ a δ i) = M.,-∘ (Sub-ind γ) (Tm-ind a) (Sub-ind δ) i

Sub-ind (S.▸-β₁ γ a i) = M.▸-β₁ (Sub-ind γ) (Tm-ind a) i
Sub-ind (S.▸-η i) = M.▸-η i

Sub-ind S.ε = M.ε
Sub-ind (S.ε-∘ γ i) = M.ε-∘ (Sub-ind γ) i
Sub-ind (S.◆-η i) = M.◆-η i

Tm-ind (S.Tm-is-set a₁ a₂ p q i j) =
  is-set→squarep
    {A = λ i j → M.Tm _ _ (S.Tm-is-set _ _ _ _ i j)}
    (λ i j → hlevel 2) refl (λ j → Tm-ind (p j)) (λ j → Tm-ind (q j)) refl i j
Tm-ind (a S.[ γ ]) = Tm-ind a M.[ Sub-ind γ ]
Tm-ind (S.[]-∘ a γ δ i) = M.[]-∘ (Tm-ind a) (Sub-ind γ) (Sub-ind δ) i
Tm-ind (S.[]-id a i) = M.[]-id (Tm-ind a) i

Tm-ind S.q = M.q
Tm-ind (S.▸-β₂ γ a i) = M.▸-β₂ (Sub-ind γ) (Tm-ind a) i

Tm-ind (S.app f a) = M.app (Tm-ind f) (Tm-ind a)
Tm-ind (S.app-[] f a γ i) = M.app-[] (Tm-ind f) (Tm-ind a) (Sub-ind γ) i

Tm-ind (S.lam a) = M.lam (Tm-ind a)
Tm-ind (S.lam-[] a γ i) = M.lam-[] (Tm-ind a) (Sub-ind γ) i

Tm-ind (S.⇒-β f a i) = M.⇒-β (Tm-ind f) (Tm-ind a) i
Tm-ind (S.⇒-η a i) = M.⇒-η (Tm-ind a) i

Tm-ind (S.⊥-rec t) = M.⊥-rec (Tm-ind t)
Tm-ind (S.⊥-rec-[] t γ i) = M.⊥-rec-[] (Tm-ind t) (Sub-ind γ) i

Tm-ind S.true = M.true
Tm-ind (S.true-[] γ i) = M.true-[] (Sub-ind γ) i

Tm-ind S.false = M.false
Tm-ind (S.false-[] γ i) = M.false-[] (Sub-ind γ) i

Tm-ind (S.Bool-rec a₁ a₂ t) = M.Bool-rec (Tm-ind a₁) (Tm-ind a₂) (Tm-ind t)
Tm-ind (S.Bool-rec-[] a₁ a₂ t γ i) =
  M.Bool-rec-[] (Tm-ind a₁) (Tm-ind a₂) (Tm-ind t) (Sub-ind γ) i

Tm-ind (S.Bool-β₁ a₁ a₂ i) = M.Bool-β₁ (Tm-ind a₁) (Tm-ind a₂) i
Tm-ind (S.Bool-β₂ a₁ a₂ i) = M.Bool-β₂ (Tm-ind a₁) (Tm-ind a₂) i
