module STLC.Standard where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.HLevel.Universe
open import 1Lab.Reflection.HLevel
import 1Lab.Prelude as P
import Data.Bool as P
import STLC.Syntax as S
open import STLC.Model
import STLC.Recursion
open Model

Standard : Model
Standard .Con = Set lzero
Standard .Sub Δ Γ = ∣ Δ ∣ → ∣ Γ ∣
Standard .Sub-is-set = hlevel!

Standard ._∘_ γ δ θ = γ (δ θ)
Standard .assoc γ δ θ = refl

Standard .id γ = γ
Standard .idr γ = refl
Standard .idl γ = refl

Standard .Ty = Set lzero
Standard .Tm Γ A = ∣ Γ ∣ → ∣ A ∣
Standard .Tm-is-set = hlevel!

Standard ._[_] a γ δ = a (γ δ)
Standard .[]-∘ a γ δ = refl
Standard .[]-id a = refl

Standard ._▸_ Γ A = el! (∣ Γ ∣ P.× ∣ A ∣)
Standard .p (γ P., a) = γ
Standard .q (γ P., a) = a

Standard ._,_ γ a δ = γ δ P., a δ
Standard .,-∘ γ a δ = refl

Standard .▸-β₁ γ a = refl
Standard .▸-β₂ γ a = refl
Standard .▸-η = refl

Standard .◆ = el! P.⊤
Standard .ε γ = P.tt
Standard .ε-∘ γ = refl
Standard .◆-η = refl

Standard ._⇒_ A B = el! (∣ A ∣ → ∣ B ∣)
Standard .app f a γ = f γ (a γ)
Standard .app-[] f a γ = refl

Standard .lam b γ a = b (γ P., a)
Standard .lam-[] b γ = refl

Standard .⇒-β b a = refl
Standard .⇒-η f = refl

Standard .⊥ = el! P.⊥
Standard .⊥-rec t γ = P.absurd (t γ)
Standard .⊥-rec-[] t γ = refl

Standard .Bool = el! P.Bool
Standard .true γ = P.true
Standard .true-[] γ = refl
Standard .false γ = P.false
Standard .false-[] γ = refl

Standard .Bool-rec a₁ a₂ t γ = P.if (a₁ γ) (a₂ γ) (t γ)
Standard .Bool-rec-[] a₁ a₂ t γ = refl

Standard .Bool-β₁ a₁ a₂ = refl
Standard .Bool-β₂ a₁ a₂ = refl

open STLC.Recursion Standard

consistency : P.¬ S.Tm S.◆ S.⊥
consistency t = Tm-rec t P.tt
