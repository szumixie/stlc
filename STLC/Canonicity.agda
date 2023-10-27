module STLC.Canonicity where

open import Prim.Type
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel.Universe
open import 1Lab.Equiv
open import 1Lab.Univalence
open import 1Lab.Reflection.Marker
open import 1Lab.Reflection.Record
open import 1Lab.Reflection.HLevel
open import Data.Nat
import 1Lab.Prelude as P
import Data.Sum as P
import Data.Bool as P

import STLC.Syntax as S
open import STLC.Displayed
import STLC.Induction

module Canonicity where
  private variable
    n : Nat
    Γˢ Δˢ : S.Con
    γˢ γ₁ˢ γ₂ˢ δˢ θˢ : S.Sub Δˢ Γˢ
    Aˢ Bˢ : S.Ty
    aˢ a₁ˢ a₂ˢ bˢ fˢ tˢ : S.Tm Γˢ Aˢ

  record Con (Γˢ : S.Con) : Type₁ where
    no-eta-equality
    field
      sem : Set lzero
      map : ∣ sem ∣ → S.Sub S.◆ Γˢ

  open Con public
  private variable Γ Δ Θ Ξ : Con Γˢ

  record Sub (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) : Type where
    no-eta-equality
    field
      sem : ∣ Δ .sem ∣ → ∣ Γ .sem ∣
      map : ∀ δ → Γ .map (sem δ) ≡ γˢ S.∘ Δ .map δ

  open Sub public
  private unquoteDecl Sub-eqv = declare-record-iso Sub-eqv (quote Sub)

  Sub-is-set : is-set (Sub Δ Γ γˢ)
  Sub-is-set = Iso→is-hlevel 2 Sub-eqv hlevel!

  instance
    H-Level-Sub : H-Level (Sub Δ Γ γˢ) (2 + n)
    H-Level-Sub = basic-instance 2 Sub-is-set

  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : Sub Δ Γ γ₁ˢ → γ₁ˢ ≡ γ₂ˢ → Sub Δ Γ γ₂ˢ → Type
  _≡ˢ[_]_ {Δ = Δ} {Γ = Γ} γ₁ γ₁ˢ≡γ₂ˢ γ₂ =
    PathP (λ i → Sub Δ Γ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  Sub-path :
    {γ₁ : Sub Δ Γ γ₁ˢ} {γ₂ : Sub Δ Γ γ₂ˢ} {γ₁ˢ≡γ₂ˢ : γ₁ˢ ≡ γ₂ˢ} →
    (∀ δ → γ₁ .sem δ ≡ γ₂ .sem δ) → γ₁ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂
  Sub-path sem-path i .sem δ = sem-path δ i
  Sub-path
    {Δ = Δ} {Γ = Γ} {γ₁ = γ₁} {γ₂ = γ₂} {γ₁ˢ≡γ₂ˢ = γ₁ˢ≡γ₂ˢ} sem-path i .map =
    prop!
      {A = λ i → ∀ δ → Γ .map (sem-path δ i) ≡ γ₁ˢ≡γ₂ˢ i S.∘ Δ .map δ}
      {x = γ₁ .map} {y = γ₂ .map} i

  infixl 40 _∘_
  _∘_ : Sub Δ Γ γˢ → Sub Θ Δ δˢ → Sub Θ Γ (γˢ S.∘ δˢ)
  (γ ∘ δ) .sem θ = γ .sem (δ .sem θ)
  _∘_ {Δ = Δ} {Γ = Γ} {γˢ = γˢ} {Θ = Θ} {δˢ = δˢ} γ δ .map θ =
    Γ .map (γ .sem (δ .sem θ))   ≡⟨ γ .map _ ⟩
    γˢ S.∘ ⌜ Δ .map (δ .sem θ) ⌝ ≡⟨ ap! (δ .map _) ⟩
    γˢ S.∘ (δˢ S.∘ Θ .map θ)     ≡⟨ S.assoc _ _ _ ⟩
    γˢ S.∘ δˢ S.∘ Θ .map θ       ∎

  assoc :
    (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) (θ : Sub Ξ Θ θˢ) →
    γ ∘ (δ ∘ θ) ≡ˢ[ S.assoc _ _ _ ] γ ∘ δ ∘ θ
  assoc γ δ θ = Sub-path λ ξ → refl

  id : Sub Γ Γ S.id
  id .sem γ = γ
  id .map γ = sym (S.idl _)

  idr : (γ : Sub Δ Γ γˢ) → γ ∘ id ≡ˢ[ S.idr _ ] γ
  idr γ = Sub-path λ δ → refl

  idl : (γ : Sub Δ Γ γˢ) → id ∘ γ ≡ˢ[ S.idl _ ] γ
  idl γ = Sub-path λ δ → refl

  record Ty (Aˢ : S.Ty) : Type₁ where
    no-eta-equality
    field
      sem : Set lzero
      map : ∣ sem ∣ → S.Tm S.◆ Aˢ

  open Ty public
  private variable A B : Ty Aˢ

  record Tm (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) : Type where
    no-eta-equality
    field
      sem : ∣ Γ .sem ∣ → ∣ A .sem ∣
      map : ∀ γ → A .map (sem γ) ≡ aˢ S.[ Γ .map γ ]

  open Tm public
  private unquoteDecl Tm-eqv = declare-record-iso Tm-eqv (quote Tm)

  Tm-is-set : is-set (Tm Γ A aˢ)
  Tm-is-set = Iso→is-hlevel 2 Tm-eqv hlevel!

  instance
    H-Level-Tm : H-Level (Tm Γ A aˢ) (2 + n)
    H-Level-Tm = basic-instance 2 Tm-is-set

  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ A} → Tm Γ A a₁ˢ → a₁ˢ ≡ a₂ˢ → Tm Γ A a₂ˢ → Type
  _≡ᵗ[_]_ {Γ = Γ} {A = A} a₁ a₁ˢ≡a₂ˢ a₂ =
    PathP (λ i → Tm Γ A (a₁ˢ≡a₂ˢ i)) a₁ a₂

  Tm-path :
    {a₁ : Tm Γ A a₁ˢ} {a₂ : Tm Γ A a₂ˢ} {a₁ˢ≡a₂ˢ : a₁ˢ ≡ a₂ˢ} →
    (∀ γ → a₁ .sem γ ≡ a₂ .sem γ) → a₁ ≡ᵗ[ a₁ˢ≡a₂ˢ ] a₂
  Tm-path sem-path i .sem γ = sem-path γ i
  Tm-path
    {Γ = Γ} {A = A} {a₁ = a₁} {a₂ = a₂} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} sem-path i .map =
    prop!
      {A = λ i → ∀ γ → A .map (sem-path γ i) ≡ a₁ˢ≡a₂ˢ i S.[ Γ .map γ ]}
      {x = a₁ .map} {y = a₂ .map} i

  infixl 40 _[_]
  _[_] : Tm Γ A aˢ → Sub Δ Γ γˢ → Tm Δ A (aˢ S.[ γˢ ])
  (a [ γ ]) .sem δ = a .sem (γ .sem δ)
  _[_] {Γ = Γ} {A = A} {aˢ = aˢ} {Δ = Δ} {γˢ = γˢ} a γ .map δ =
    A .map (a .sem (γ .sem δ))     ≡⟨ a .map _ ⟩
    aˢ S.[ ⌜ Γ .map (γ .sem δ) ⌝ ] ≡⟨ ap! (γ .map _) ⟩
    aˢ S.[ γˢ S.∘ Δ .map δ ]       ≡⟨ S.[]-∘ _ _ _ ⟩
    aˢ S.[ γˢ ] S.[ Δ .map δ ]     ∎

  []-∘ :
    (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) →
    a [ γ ∘ δ ] ≡ᵗ[ S.[]-∘ _ _ _ ] a [ γ ] [ δ ]
  []-∘ a γ δ = Tm-path λ θ → refl

  []-id : (a : Tm Γ A aˢ) → a [ id ] ≡ᵗ[ S.[]-id _ ] a
  []-id a = Tm-path λ γ → refl

  infixl 4 _▸_
  _▸_ : Con Γˢ → Ty Aˢ → Con (Γˢ S.▸ Aˢ)
  (Γ ▸ A) .sem = el! (∣ Γ .sem ∣ P.× ∣ A .sem ∣)
  (Γ ▸ A) .map (γ P., a) = Γ .map γ S., A .map a

  p : Sub (Γ ▸ A) Γ S.p
  p .sem (γ P., a) = γ
  p .map (γ P., a) = sym (S.▸-β₁ _ _)

  q : Tm (Γ ▸ A) A S.q
  q .sem (γ P., a) = a
  q .map (γ P., a) = sym (S.▸-β₂ _ _)

  infixl 4 _,_
  _,_ : Sub Δ Γ γˢ → Tm Δ A aˢ → Sub Δ (Γ ▸ A) (γˢ S., aˢ)
  (γ , a) .sem δ = γ .sem δ P., a .sem δ
  _,_ {Δ = Δ} {Γ = Γ} {γˢ = γˢ} {A = A} {aˢ = aˢ} γ a .map δ =
    ⌜ Γ .map (γ .sem δ) ⌝ S., A .map (a .sem δ) ≡⟨ ap! (γ .map _) ⟩
    γˢ S.∘ Δ .map δ S., ⌜ A .map (a .sem δ) ⌝   ≡⟨ ap! (a .map _) ⟩
    γˢ S.∘ Δ .map δ S., aˢ S.[ Δ .map δ ]       ≡˘⟨ S.,-∘ _ _ _ ⟩
    (γˢ S., aˢ) S.∘ Δ .map δ                    ∎

  ,-∘ :
    (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) (δ : Sub Θ Δ δˢ) →
    (γ , a) ∘ δ ≡ˢ[ S.,-∘ _ _ _ ] (γ ∘ δ , a [ δ ])
  ,-∘ γ a δ = Sub-path λ θ → refl

  ▸-β₁ :
    ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
    p ∘ (γ , a) ≡ˢ[ S.▸-β₁ _ _ ] γ
  ▸-β₁ γ a = Sub-path λ δ → refl

  ▸-β₂ :
    ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
    q [ γ , a ] ≡ᵗ[ S.▸-β₂ _ _ ] a
  ▸-β₂ γ a = Tm-path λ δ → refl

  ▸-η : (p , q) ≡ˢ[ S.▸-η ] id {Γ = Γ ▸ A}
  ▸-η = Sub-path λ (γ P., a) → refl

  ◆ : Con S.◆
  ◆ .sem = el! P.⊤
  ◆ .map P.tt = S.ε

  ε : Sub Γ ◆ S.ε
  ε .sem γ = P.tt
  ε .map γ = sym (S.ε-∘ _)

  ε-∘ : (γ : Sub Δ Γ γˢ) → ε ∘ γ ≡ˢ[ S.ε-∘ _ ] ε
  ε-∘ γ = Sub-path λ δ → refl

  ◆-η : ε ≡ˢ[ S.◆-η ] id
  ◆-η = Sub-path λ _ → refl

  infixl 4 _↑
  _↑ : Sub Δ Γ γˢ → Sub (Δ ▸ A) (Γ ▸ A) (γˢ S.↑)
  γ ↑ = γ ∘ p , q

  ⟨_⟩ : Tm Γ A aˢ → Sub Γ (Γ ▸ A) S.⟨ aˢ ⟩
  ⟨_⟩ = id ,_

  record Fun (A : Ty Aˢ) (B : Ty Bˢ) : Type where
    no-eta-equality
    field
      syn : S.Tm S.◆ (Aˢ S.⇒ Bˢ)
      sem : ∣ A .sem ∣ → ∣ B .sem ∣
      map : ∀ a → B .map (sem a) ≡ S.app syn (A .map a)

  open Fun public
  private unquoteDecl Fun-eqv = declare-record-iso Fun-eqv (quote Fun)

  Fun-is-set : is-set (Fun A B)
  Fun-is-set = Iso→is-hlevel 2 Fun-eqv hlevel!

  instance
    H-Level-Fun : H-Level (Fun A B) (2 + n)
    H-Level-Fun = basic-instance 2 Fun-is-set

  Fun-path :
    {f₁ f₂ : Fun A B} →
    f₁ .syn ≡ f₂ .syn → (∀ a → f₁ .sem a ≡ f₂ .sem a) → f₁ ≡ f₂
  Fun-path syn-path sem-path i .syn = syn-path i
  Fun-path syn-path sem-path i .sem a = sem-path a i
  Fun-path {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .map =
    prop!
      {A = λ i → ∀ a → B .map (sem-path a i) ≡ S.app (syn-path i) (A .map a)}
      {x = f₁ .map} {y = f₂ .map} i

  infixr 0 _⇒_
  _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.⇒ Bˢ)
  (A ⇒ B) .sem = el! (Fun A B)
  (A ⇒ B) .map = syn

  app : Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (S.app fˢ aˢ)
  app f a .sem γ = f .sem γ .sem (a .sem γ)
  app {Γ = Γ} {A = A} {B = B} {fˢ = fˢ} {aˢ = aˢ} f a .map γ =
    B .map (f .sem γ .sem (a .sem γ))               ≡⟨ f .sem _ .map _ ⟩
    S.app ⌜ f .sem γ .syn ⌝ (A .map (a .sem γ))     ≡⟨ ap! (f .map _) ⟩
    S.app (fˢ S.[ Γ .map γ ]) ⌜ A .map (a .sem γ) ⌝ ≡⟨ ap! (a .map _) ⟩
    S.app (fˢ S.[ Γ .map γ ]) (aˢ S.[ Γ .map γ ])   ≡˘⟨ S.app-[] _ _ _ ⟩
    S.app fˢ aˢ S.[ Γ .map γ ]                      ∎

  app-[] :
    (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
    app f a [ γ ] ≡ᵗ[ S.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])
  app-[] f a γ = Tm-path λ δ → refl

  lam : Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (S.lam bˢ)
  lam {Γ = Γ} {bˢ = bˢ} b .sem γ .syn = S.lam bˢ S.[ Γ .map γ ]
  lam b .sem γ .sem a = b .sem (γ P., a)
  lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b .sem γ .map a =
    B .map (b .sem (γ P., a))                          ≡⟨ b .map _ ⟩
    bˢ S.[ ⌜ Γ .map γ S., A .map a ⌝ ]                 ≡˘⟨ ap¡ (S.↑-⟨⟩ _ _) ⟩
    bˢ S.[ (Γ .map γ S.↑) S.∘ S.⟨ A .map a ⟩ ]         ≡⟨ S.[]-∘ _ _ _ ⟩
    bˢ S.[ Γ .map γ S.↑ ] S.[ S.⟨ A .map a ⟩ ]         ≡˘⟨ S.⇒-β _ _ ⟩
    S.app ⌜ S.lam (bˢ S.[ Γ .map γ S.↑ ]) ⌝ (A .map a) ≡˘⟨ ap¡ (S.lam-[] _ _) ⟩
    S.app (S.lam bˢ S.[ Γ .map γ ]) (A .map a)         ∎
  lam b .map γ = refl

  lam-[] :
    (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
    lam b [ γ ] ≡ᵗ[ S.lam-[] _ _ ] lam (b [ γ ↑ ])
  lam-[] {Γ = Γ} {bˢ = bˢ} {Δ = Δ} {γˢ} b γ = Tm-path λ δ →
    Fun-path
      ( S.lam bˢ S.[ ⌜ Γ .map (γ .sem δ) ⌝ ]   ≡⟨ ap! (γ .map _) ⟩
        S.lam bˢ S.[ γˢ S.∘ Δ .map δ ]         ≡⟨ S.[]-∘ _ _ _ ⟩
        ⌜ S.lam bˢ S.[ γˢ ] ⌝ S.[ Δ .map δ ]   ≡⟨ ap! (S.lam-[] _ _) ⟩
        S.lam (bˢ S.[ γˢ S.↑ ]) S.[ Δ .map δ ] ∎)
      λ a → refl

  ⇒-β :
    (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
    app (lam b) a ≡ᵗ[ S.⇒-β _ _ ] b [ ⟨ a ⟩ ]
  ⇒-β b a = Tm-path λ γ → refl

  ⇒-η : (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ S.⇒-η _ ] f
  ⇒-η {Γ = Γ} {fˢ = fˢ} f = Tm-path λ γ →
    Fun-path
      ( ⌜ S.lam (S.app (fˢ S.[ S.p ]) S.q) ⌝ S.[ Γ .map γ ] ≡⟨ ap! (S.⇒-η _) ⟩
        fˢ S.[ Γ .map γ ]                                   ≡˘⟨ f .map _ ⟩
        f .sem γ .syn                                       ∎)
      λ a → refl

  ⊥ : Ty S.⊥
  ⊥ .sem = el! P.⊥
  ⊥ .map ()

  ⊥-rec : Tm Γ ⊥ tˢ → Tm Γ A (S.⊥-rec tˢ)
  ⊥-rec t .sem γ = P.absurd (t .sem γ)
  ⊥-rec t .map γ = P.absurd (t .sem γ)

  ⊥-rec-[] :
    (t : Tm Γ ⊥ tˢ) (γ : Sub Δ Γ γˢ) →
    ⊥-rec {A = A} t [ γ ] ≡ᵗ[ S.⊥-rec-[] _ _ ] ⊥-rec (t [ γ ])
  ⊥-rec-[] t γ = Tm-path λ δ → refl

  Bool : Ty S.Bool
  Bool .sem = el! P.Bool
  Bool .map P.true = S.true
  Bool .map P.false = S.false

  true : Tm Γ Bool S.true
  true .sem γ = P.true
  true .map γ = sym (S.true-[] _)

  true-[] : (γ : Sub Δ Γ γˢ) → true [ γ ] ≡ᵗ[ S.true-[] _ ] true
  true-[] γ = Tm-path λ δ → refl

  false : Tm Γ Bool S.false
  false .sem γ = P.false
  false .map γ = sym (S.false-[] _)

  false-[] : (γ : Sub Δ Γ γˢ) → false [ γ ] ≡ᵗ[ S.false-[] _ ] false
  false-[] γ = Tm-path λ δ → refl

  Bool-rec :
    Tm Γ A a₁ˢ → Tm Γ A a₂ˢ → Tm Γ Bool tˢ → Tm Γ A (S.Bool-rec a₁ˢ a₂ˢ tˢ)
  Bool-rec a₁ a₂ t .sem γ = P.if (a₁ .sem γ) (a₂ .sem γ) (t .sem γ)
  Bool-rec {Γ = Γ} {A = A} {a₁ˢ = a₁ˢ} {a₂ˢ = a₂ˢ} {tˢ = tˢ} a₁ a₂ t .map γ =
    A .map (P.if (a₁ .sem γ) (a₂ .sem γ) (t .sem γ))                              ≡⟨ Bool-rec-map _ _ _ ⟩
    S.Bool-rec ⌜ A .map (a₁ .sem γ) ⌝ (A .map (a₂ .sem γ)) (Bool .map (t .sem γ)) ≡⟨ ap! (a₁ .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) ⌜ A .map (a₂ .sem γ) ⌝ (Bool .map (t .sem γ)) ≡⟨ ap! (a₂ .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) (a₂ˢ S.[ Γ .map γ ]) ⌜ Bool .map (t .sem γ) ⌝ ≡⟨ ap! (t .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) (a₂ˢ S.[ Γ .map γ ]) (tˢ S.[ Γ .map γ ])      ≡˘⟨ S.Bool-rec-[] _ _ _ _ ⟩
    S.Bool-rec a₁ˢ a₂ˢ tˢ S.[ Γ .map γ ]                                          ∎
    where
    Bool-rec-map :
      ∀ a₁ a₂ t →
       A .map (P.if a₁ a₂ t) ≡ S.Bool-rec (A .map a₁) (A .map a₂) (Bool .map t)
    Bool-rec-map a₁ a₂ P.true = sym (S.Bool-β₁ _ _)
    Bool-rec-map a₁ a₂ P.false = sym (S.Bool-β₂ _ _)

  Bool-rec-[] :
    (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) (t : Tm Γ Bool tˢ) (γ : Sub Δ Γ γˢ) →
    Bool-rec a₁ a₂ t [ γ ] ≡ᵗ[ S.Bool-rec-[] _ _ _ _ ]
    Bool-rec (a₁ [ γ ]) (a₂ [ γ ]) (t [ γ ])
  Bool-rec-[] a₁ a₂ t γ = Tm-path λ δ → refl

  Bool-β₁ :
    (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) →
    Bool-rec a₁ a₂ true ≡ᵗ[ S.Bool-β₁ _ _ ] a₁
  Bool-β₁ a₁ a₂ = Tm-path λ γ → refl

  Bool-β₂ :
    (a₁ : Tm Γ A a₁ˢ) (a₂ : Tm Γ A a₂ˢ) →
    Bool-rec a₁ a₂ false ≡ᵗ[ S.Bool-β₂ _ _ ] a₂
  Bool-β₂ a₁ a₂ = Tm-path λ γ → refl

open Canonicity

Canonicity : Displayed
Canonicity = record {Canonicity}

open STLC.Induction Canonicity

canonicalize : S.Tm S.◆ S.Bool → P.Bool
canonicalize t = Tm-ind t .sem P.tt

completeness : ∀ t → Bool .map (canonicalize t) ≡ t
completeness t =
  Bool .map (Tm-ind t .sem P.tt) ≡⟨ Tm-ind t .map P.tt ⟩
  t S.[ ⌜ S.ε ⌝ ]                ≡⟨ ap! S.◆-η ⟩
  t S.[ S.id ]                   ≡⟨ S.[]-id _ ⟩
  t                              ∎

stability : ∀ t → canonicalize (Bool .map t) ≡ t
stability P.true = refl
stability P.false = refl

Tm≃Bool : S.Tm S.◆ S.Bool ≃ P.Bool
Tm≃Bool = Iso→Equiv (canonicalize P., (iso (Bool .map) stability completeness))

canonicity : (t : S.Tm S.◆ S.Bool) → t ≡ S.true P.⊎ t ≡ S.false
canonicity t = map→⊎ (canonicalize t) (completeness t)
  where
  map→⊎ : (t′ : P.Bool) → Bool .map t′ ≡ t → t ≡ S.true P.⊎ t ≡ S.false
  map→⊎ P.true p = P.inl (sym p)
  map→⊎ P.false p = P.inr (sym p)
