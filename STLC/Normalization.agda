module STLC.Normalization where

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
open import Data.Dec
open import Data.Nat
import 1Lab.Prelude as P
import Data.Sum as P
import Data.Bool as P

import STLC.Syntax as S
open import STLC.Weakening as W
  using (Wk; Wk-emb; Wk-emb-∘; Wk-emb-id; Var; Var-emb)
open import STLC.NormalForm as N
  using
    ( Ne; Nf; Discrete-Nf; Ne-emb; Nf-emb;
      _[_]ᴺᵉ; _[_]ᴺᶠ; Ne-emb-[]; Nf-emb-[]; []ᴺᵉ-∘; []ᴺᵉ-id; []ᴺᶠ-∘; []ᴺᶠ-id)
open import STLC.Displayed
import STLC.Induction

module Normalization where
  private variable
    n : Nat
    X Y Z : S.Con
    Γˢ Δˢ : S.Con
    γˢ γ₁ˢ γ₂ˢ δˢ θˢ : S.Sub Δˢ Γˢ
    Aˢ Bˢ : S.Ty
    aˢ a₁ˢ a₂ˢ bˢ fˢ tˢ : S.Tm Γˢ Aˢ

  record Con (Γˢ : S.Con) : Type₁ where
    no-eta-equality
    infixl 40 _[_]
    field
      sem : S.Con → Set lzero
      _[_] : ∣ sem X ∣ → Wk Y X → ∣ sem Y ∣
      ![]-∘ : ∀ γ (x : Wk Y X) (y : Wk Z Y) → γ [ x W.∘ y ] ≡ γ [ x ] [ y ]
      ![]-id : (γ : ∣ sem X ∣) → γ [ W.id ] ≡ γ

      map : ∣ sem X ∣ → S.Sub X Γˢ
      map-[] : ∀ γ (x : Wk Y X) → map (γ [ x ]) ≡ map γ S.∘ Wk-emb x

  open Con public renaming (_[_] to _!_[_])
  private variable Γ Δ Θ Ξ : Con Γˢ

  record Sub (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) : Type where
    no-eta-equality
    module Δ = Con Δ
    field
      sem : ∣ Δ .sem X ∣ → ∣ Γ .sem X ∣
      ![] : ∀ δ (x : Wk Y X) → sem (Δ ! δ [ x ]) ≡ Γ ! sem δ [ x ]
      map : (δ : ∣ Δ.sem X ∣) → Γ .map (sem δ) ≡ γˢ S.∘ Δ .map δ

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
    (∀ {X} (δ : ∣ Δ .sem X ∣) → γ₁ .sem δ ≡ γ₂ .sem δ) → γ₁ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂
  Sub-path sem-path i .sem δ = sem-path δ i
  Sub-path {Δ = Δ} {Γ = Γ} {γ₁ = γ₁} {γ₂ = γ₂} sem-path i .![] =
    prop!
      {A = λ i → ∀ {Y} {X} δ (x : Wk Y X) →
        sem-path (Δ ! δ [ x ]) i ≡ Γ ! sem-path δ i [ x ]}
      {x = γ₁ .![]}  {y = γ₂ .![]} i
  Sub-path
    {Δ = Δ} {Γ = Γ} {γ₁ = γ₁} {γ₂ = γ₂} {γ₁ˢ≡γ₂ˢ = γ₁ˢ≡γ₂ˢ} sem-path i .map =
    prop!
      {A = λ i → ∀ δ → Γ .map (sem-path δ i) ≡ γ₁ˢ≡γ₂ˢ i S.∘ Δ .map δ}
      {x = γ₁ .map} {y = γ₂ .map} i

  infixl 40 _∘_
  _∘_ : Sub Δ Γ γˢ → Sub Θ Δ δˢ → Sub Θ Γ (γˢ S.∘ δˢ)
  (γ ∘ δ) .sem θ = γ .sem (δ .sem θ)
  _∘_ {Δ = Δ} {Γ = Γ} {Θ = Θ} γ δ .![] θ x =
    γ .sem ⌜ δ .sem (Θ ! θ [ x ]) ⌝ ≡⟨ ap! (δ .![] _ _) ⟩
    γ .sem (Δ ! δ .sem θ [ x ])     ≡⟨ γ .![] _ _ ⟩
    Γ ! γ .sem (δ .sem θ) [ x ]     ∎
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
  id .![] γ x = refl
  id .map γ = sym (S.idl _)

  idr : (γ : Sub Δ Γ γˢ) → γ ∘ id ≡ˢ[ S.idr _ ] γ
  idr γ = Sub-path λ δ → refl

  idl : (γ : Sub Δ Γ γˢ) → id ∘ γ ≡ˢ[ S.idl _ ] γ
  idl γ = Sub-path λ δ → refl

  record Ty (Aˢ : S.Ty) : Type₁ where
    no-eta-equality
    infixl 40 _[_]
    field
      sem : S.Con → Set lzero
      _[_] : ∣ sem X ∣ → Wk Y X → ∣ sem Y ∣
      ![]-∘ : ∀ a (x : Wk Y X) (y : Wk Z Y) → a [ x W.∘ y ] ≡ a [ x ] [ y ]
      ![]-id : (a : ∣ sem X ∣) → a [ W.id ] ≡ a

      map : ∣ sem X ∣ → S.Tm X Aˢ
      map-[] : ∀ a (x : Wk Y X) → map (a [ x ]) ≡ map a S.[ Wk-emb x ]

      quo : ∣ sem X ∣ → Nf X Aˢ
      quo-[] : ∀ a (x : Wk Y X) → quo (a [ x ]) ≡ quo a [ x ]ᴺᶠ
      emb-quo : (a : ∣ sem X ∣) → Nf-emb (quo a) ≡ map a

      ref : Ne X Aˢ → ∣ sem X ∣
      ref-[] : ∀ a (x : Wk Y X) → ref (a [ x ]ᴺᵉ) ≡ ref a [ x ]
      map-ref : (a : Ne X Aˢ) → map (ref a) ≡ Ne-emb a

  open Ty public renaming (_[_] to _!_[_])
  private variable A B : Ty Aˢ

  record Tm (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) : Type where
    no-eta-equality
    module Γ = Con Γ
    field
      sem : ∣ Γ .sem X ∣ → ∣ A .sem X ∣
      ![] : ∀ γ (x : Wk Y X) → sem (Γ ! γ [ x ]) ≡ A ! sem γ [ x ]
      map : (γ : ∣ Γ.sem X ∣) → A .map (sem γ) ≡ aˢ S.[ Γ .map γ ]

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
    (∀ {X} (γ : ∣ Γ .sem X ∣) → a₁ .sem γ ≡ a₂ .sem γ) → a₁ ≡ᵗ[ a₁ˢ≡a₂ˢ ] a₂
  Tm-path sem-path i .sem γ = sem-path γ i
  Tm-path {Γ = Γ} {A = A} {a₁ = a₁} {a₂ = a₂} sem-path i .![] =
    prop!
      {A = λ i → ∀ {Y} {X} γ (x : Wk Y X) →
        sem-path (Γ ! γ [ x ]) i ≡ A ! sem-path γ i [ x ]}
      {x = a₁ .![]}  {y = a₂ .![]} i
  Tm-path
    {Γ = Γ} {A = A} {a₁ = a₁} {a₂ = a₂} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} sem-path i .map =
    prop!
      {A = λ i → ∀ γ → A .map (sem-path γ i) ≡ a₁ˢ≡a₂ˢ i S.[ Γ .map γ ]}
      {x = a₁ .map} {y = a₂ .map} i

  infixl 40 _[_]
  _[_] : Tm Γ A aˢ → Sub Δ Γ γˢ → Tm Δ A (aˢ S.[ γˢ ])
  (a [ γ ]) .sem δ = a .sem (γ .sem δ)
  _[_] {Γ = Γ} {A = A} {Δ = Δ} a γ .![] δ x =
    a .sem ⌜ γ .sem (Δ ! δ [ x ]) ⌝ ≡⟨ ap! (γ .![] _ _) ⟩
    a .sem (Γ ! γ .sem δ [ x ])     ≡⟨ a .![] _ _ ⟩
    A ! a .sem (γ .sem δ) [ x ]     ∎
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
  (Γ ▸ A) .sem X = el! (∣ Γ .sem X ∣ P.× ∣ A .sem X ∣)
  (Γ ▸ A) ! (γ P., a) [ x ] = Γ ! γ [ x ] P., A ! a [ x ]
  (Γ ▸ A) .![]-∘ (γ P., a) x y = P.Σ-pathp (Γ .![]-∘ γ x y) (A .![]-∘ a x y)
  (Γ ▸ A) .![]-id (γ P., a) = Σ-pathp (Γ .![]-id γ) (A .![]-id a)

  (Γ ▸ A) .map (γ P., a) = Γ .map γ S., A .map a
  (Γ ▸ A) .map-[] (γ P., a) x =
    ⌜ Γ .map (Γ ! γ [ x ]) ⌝ S., A .map (A ! a [ x ])  ≡⟨ ap! (Γ .map-[] _ _) ⟩
    Γ .map γ S.∘ Wk-emb x S., ⌜ A .map (A ! a [ x ]) ⌝ ≡⟨ ap! (A .map-[] _ _) ⟩
    Γ .map γ S.∘ Wk-emb x S., A .map a S.[ Wk-emb x ]  ≡˘⟨ S.,-∘ _ _ _ ⟩
    (Γ .map γ S., A .map a) S.∘ Wk-emb x               ∎

  p : Sub (Γ ▸ A) Γ S.p
  p .sem = P.fst
  p .![] (γ P., a) x = refl
  p .map (γ P., a) = sym (S.▸-β₁ _ _)

  q : Tm (Γ ▸ A) A S.q
  q .sem = P.snd
  q .![] (γ P., a) x = refl
  q .map (γ P., a) = sym (S.▸-β₂ _ _)

  infixl 4 _,_
  _,_ : Sub Δ Γ γˢ → Tm Δ A aˢ → Sub Δ (Γ ▸ A) (γˢ S., aˢ)
  (γ , a) .sem δ = γ .sem δ P., a .sem δ
  (γ , a) .![] δ x = Σ-pathp (γ .![] δ x) (a .![] δ x)
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
  ◆ .sem X = el! P.⊤
  ◆ ! P.tt [ x ] = P.tt
  ◆ .![]-∘ P.tt x y = refl
  ◆ .![]-id P.tt = refl

  ◆ .map P.tt = S.ε
  ◆ .map-[] P.tt x = sym (S.ε-∘ _)

  ε : Sub Γ ◆ S.ε
  ε .sem γ = P.tt
  ε .![] γ x = refl
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

  record Fun (X : S.Con) (A : Ty Aˢ) (B : Ty Bˢ) : Type where
    no-eta-equality
    module A = Ty A
    field
      syn : S.Tm X (Aˢ S.⇒ Bˢ)
      sem : Wk Y X → ∣ A .sem Y ∣ → ∣ B .sem Y ∣
      ![] :
        ∀ (x : Wk Y X) a (y : Wk Z Y) →
        sem (x W.∘ y) (A ! a [ y ]) ≡ B ! sem x a [ y ]
      map :
        ∀ (x : Wk Y X) a →
        B .map (sem x a) ≡ S.app (syn S.[ Wk-emb x ]) (A .map a)

  open Fun public
  private unquoteDecl Fun-eqv = declare-record-iso Fun-eqv (quote Fun)

  Fun-is-set : is-set (Fun X A B)
  Fun-is-set = Iso→is-hlevel 2 Fun-eqv hlevel!

  instance
    H-Level-Fun : H-Level (Fun X A B) (2 + n)
    H-Level-Fun = basic-instance 2 Fun-is-set

  Fun-path :
    ∀ {f₁ f₂ : Fun X A B} →
    f₁ .syn ≡ f₂ .syn →
    (∀ {Y} (x : Wk Y X) (a : ∣ A .sem Y ∣) → f₁ .sem x a ≡ f₂ .sem x a) →
    f₁ ≡ f₂
  Fun-path syn-path sem-path i .syn = syn-path i
  Fun-path syn-path sem-path i .sem x a = sem-path x a i
  Fun-path
    {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .![] =
    prop!
      {A = λ i → ∀ {Z} {Y} (x : Wk Y X) a (y : Wk Z Y) →
        sem-path (x W.∘ y) (A ! a [ y ]) i ≡ B ! sem-path x a i [ y ]}
      {x = f₁ .![]}  {y = f₂ .![]} i
  Fun-path
    {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .map =
    prop!
      {A = λ i → ∀ {Y} (x : Wk Y X) a →
        B .map (sem-path x a i) ≡ S.app (syn-path i S.[ Wk-emb x ]) (A .map a)}
      {x = f₁ .map} {y = f₂ .map} i

  infixr 0 _⇒_
  _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.⇒ Bˢ)
  (A ⇒ B) .sem X = el! (Fun X A B)
  ((A ⇒ B) ! f [ x ]) .syn = f .syn S.[ Wk-emb x ]
  ((A ⇒ B) ! f [ x ]) .sem y a = f .sem (x W.∘ y) a
  ((A ⇒ B) ! f [ x ]) .![] y a z =
    f .sem ⌜ x W.∘ (y W.∘ z) ⌝ (A ! a [ z ]) ≡⟨ ap! (W.assoc x y z) ⟩
    f .sem (x W.∘ y W.∘ z) (A ! a [ z ])     ≡⟨ f .![] (x W.∘ y) a z ⟩
    B ! f .sem (x W.∘ y) a [ z ]             ∎
  ((A ⇒ B) ! f [ x ]) .map y a =
    B .map (f .sem (x W.∘ y) a)                             ≡⟨ f .map (x W.∘ y) a ⟩
    S.app (f .syn S.[ ⌜ Wk-emb (x W.∘ y) ⌝ ]) (A .map a)    ≡⟨ ap! (Wk-emb-∘ _ _) ⟩
    S.app ⌜ f .syn S.[ Wk-emb x S.∘ Wk-emb y ] ⌝ (A .map a) ≡⟨ ap! (S.[]-∘ _ _ _) ⟩
    S.app (f .syn S.[ Wk-emb x ] S.[ Wk-emb y ]) (A .map a) ∎
  (A ⇒ B) .![]-∘ f x y =
    Fun-path
      ( f .syn S.[ ⌜  Wk-emb (x W.∘ y) ⌝ ]   ≡⟨ ap! (Wk-emb-∘ _ _) ⟩
        f .syn S.[ Wk-emb x S.∘ Wk-emb y ]   ≡⟨ S.[]-∘ _ _ _ ⟩
        f .syn S.[ Wk-emb x ] S.[ Wk-emb y ] ∎)
      λ z a → ap (f .sem) (sym (W.assoc x y z)) $ₚ _
  (A ⇒ B) .![]-id f =
    Fun-path
      ( f .syn S.[ ⌜ Wk-emb W.id ⌝ ] ≡⟨ ap! Wk-emb-id ⟩
        f .syn S.[ S.id ]            ≡⟨ S.[]-id _ ⟩
        f .syn                       ∎)
      λ x a → ap (f .sem) (W.idl _) $ₚ _

  (A ⇒ B) .map = syn
  (A ⇒ B) .map-[] f x = refl

  (A ⇒ B) .quo f = N.lam (B .quo (f .sem (W.id W.∘p) (A .ref (N.var W.q))))
  (A ⇒ B) .quo-[] f x =
    Nf.lam (B .quo (f .sem (⌜ x W.∘ W.id ⌝ Wk.∘p) (A .ref (Ne.var W.q))))              ≡⟨ ap! (W.idr _) ⟩
    Nf.lam (B .quo (f .sem (⌜ x ⌝ Wk.∘p) (A .ref (Ne.var W.q))))                       ≡˘⟨ ap¡ (W.idl _) ⟩
    Nf.lam (B .quo (f .sem (W.id W.∘ x Wk.∘p) ⌜ A .ref (Ne.var W.q) ⌝))                ≡⟨ ap! (A .ref-[] _ _) ⟩
    Nf.lam (B .quo ⌜ f .sem (W.id W.∘ x Wk.∘p) (A ! A .ref (Ne.var W.q) [ x Wk.↑ ]) ⌝) ≡⟨ ap! (f .![] _ _ _) ⟩
    Nf.lam ⌜ B .quo (B ! f .sem (W.id Wk.∘p) (A .ref (Ne.var W.q)) [ x Wk.↑ ]) ⌝       ≡⟨ ap! (B .quo-[] _ _) ⟩
    Nf.lam (B .quo (f .sem (W.id Wk.∘p) (A .ref (Ne.var W.q))) [ x Wk.↑ ]ᴺᶠ)           ∎
  (A ⇒ B) .emb-quo f =
    S.lam ⌜ Nf-emb (B .quo (f .sem (W.id Wk.∘p) (A .ref (Ne.var W.q)))) ⌝               ≡⟨ ap! (B .emb-quo _) ⟩
    S.lam ⌜ B .map (f .sem (W.id Wk.∘p) (A .ref (Ne.var W.q))) ⌝                        ≡⟨ ap! (f .map _ _) ⟩
    S.lam (S.app (f .syn S.[ ⌜ Wk-emb W.id ⌝ S.∘ S.p ]) (A .map (A .ref (Ne.var W.q)))) ≡⟨ ap! Wk-emb-id ⟩
    S.lam (S.app (f .syn S.[ ⌜ S.id S.∘ S.p ⌝ ]) (A .map (A .ref (Ne.var W.q))))        ≡⟨ ap! (S.idl _) ⟩
    S.lam (S.app (f .syn S.[ S.p ]) ⌜ A .map (A .ref (Ne.var W.q)) ⌝)                   ≡⟨ ap! (A .map-ref _) ⟩
    S.lam (S.app (f .syn S.[ S.p ]) S.q)                                                ≡⟨ S.⇒-η _ ⟩
    f .syn                                                                              ∎

  (A ⇒ B) .ref f .syn = Ne-emb f
  (A ⇒ B) .ref f .sem x a = B .ref (N.app (f [ x ]ᴺᵉ) (A .quo a))
  (A ⇒ B) .ref f .![] x a y =
    B .ref (Ne.app ⌜ f [ x W.∘ y ]ᴺᵉ ⌝ (A .quo (A ! a [ y ])))   ≡⟨ ap! ([]ᴺᵉ-∘ _ _ _) ⟩
    B .ref (Ne.app (f [ x ]ᴺᵉ [ y ]ᴺᵉ) ⌜ A .quo (A ! a [ y ]) ⌝) ≡⟨ ap! (A .quo-[] _ _) ⟩
    B .ref (Ne.app (f [ x ]ᴺᵉ [ y ]ᴺᵉ) (A .quo a [ y ]ᴺᶠ))       ≡⟨ B .ref-[] _ _ ⟩
    B ! B .ref (Ne.app (f [ x ]ᴺᵉ) (A .quo a)) [ y ]             ∎
  (A ⇒ B) .ref f .map x a =
    B .map (B .ref (Ne.app (f [ x ]ᴺᵉ) (A .quo a)))       ≡⟨ B .map-ref _ ⟩
    S.app ⌜ Ne-emb (f [ x ]ᴺᵉ) ⌝ (Nf-emb (A .quo a))      ≡⟨ ap! (Ne-emb-[] f _) ⟩
    S.app (Ne-emb f S.[ Wk-emb x ]) ⌜ Nf-emb (A .quo a) ⌝ ≡⟨ ap! (A .emb-quo _) ⟩
    S.app (Ne-emb f S.[ Wk-emb x ]) (A .map a)            ∎
  (A ⇒ B) .ref-[] f x = Fun-path (Ne-emb-[] f _) λ y a →
    ap (B .ref) (ap Ne.app (sym ([]ᴺᵉ-∘ _ _ _)) $ₚ _)
  (A ⇒ B) .map-ref f = refl

  app : Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (S.app fˢ aˢ)
  app f a .sem γ = f .sem γ .sem W.id (a .sem γ)
  app {Γ = Γ} {A = A} {B = B} f a .![] γ x =
    ⌜ f .sem (Γ ! γ [ x ]) ⌝ .sem W.id (a .sem (Γ ! γ [ x ])) ≡⟨ ap! (f .![] γ x) ⟩
    f .sem γ .sem ⌜ x W.∘ W.id ⌝ (a .sem (Γ ! γ [ x ]))       ≡⟨ ap! (W.idr _) ⟩
    f .sem γ .sem ⌜ x ⌝ (a .sem (Γ ! γ [ x ]))                ≡˘⟨ ap¡ (W.idl _) ⟩
    f .sem γ .sem (W.id W.∘ x) ⌜ a .sem (Γ ! γ [ x ]) ⌝       ≡⟨ ap! (a .![] _ _) ⟩
    f .sem γ .sem (W.id W.∘ x) (A ! a .sem γ [ x ])           ≡⟨ f .sem γ .![] _ _ _ ⟩
    B ! f .sem γ .sem W.id (a .sem γ) [ x ]                   ∎
  app {Γ = Γ} {A = A} {B = B} {fˢ = fˢ} {aˢ = aˢ} f a .map γ =
    B .map (f .sem γ .sem W.id (a .sem γ))                          ≡⟨ f .sem γ .map _ _ ⟩
    S.app (f .sem γ .syn S.[ ⌜ Wk-emb W.id ⌝ ]) (A .map (a .sem γ)) ≡⟨ ap! Wk-emb-id ⟩
    S.app ⌜ f .sem γ .syn S.[ S.id ] ⌝ (A .map (a .sem γ))          ≡⟨ ap! (S.[]-id _) ⟩
    S.app ⌜ f .sem γ .syn ⌝ (A .map (a .sem γ))                     ≡⟨ ap! (f .map _) ⟩
    S.app (fˢ S.[ Γ .map γ ]) ⌜ A .map (a .sem γ) ⌝                 ≡⟨ ap! (a .map _) ⟩
    S.app (fˢ S.[ Γ .map γ ]) (aˢ S.[ Γ .map γ ])                   ≡˘⟨ S.app-[] _ _ _ ⟩
    S.app fˢ aˢ S.[ Γ .map γ ]                                      ∎

  app-[] :
    (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
    app f a [ γ ] ≡ᵗ[ S.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])
  app-[] f a γ = Tm-path λ δ → refl

  lam : Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (S.lam bˢ)
  lam {Γ = Γ} {bˢ = bˢ} b .sem γ .syn = S.lam bˢ S.[ Γ .map γ ]
  lam {Γ = Γ} b .sem γ .sem x a = b .sem (Γ ! γ [ x ] P., a)
  lam {Γ = Γ} {A = A} {B = B} b .sem γ .![] x a y =
    b .sem (⌜ Γ ! γ [ x W.∘ y ] ⌝ P., A ! a [ y ])   ≡⟨ ap! (Γ .![]-∘ _ _ _) ⟩
    b .sem (Γ ! (Γ ! γ [ x ]) [ y ] P., A ! a [ y ]) ≡⟨ b .![] _ _ ⟩
    B ! b .sem (Γ ! γ [ x ] P., a) [ y ]             ∎
  lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b .sem γ .map x a =
    B .map (b .sem (Γ ! γ [ x ] P., a))                            ≡⟨ b .map _ ⟩
    bˢ S.[ ⌜ Γ .map (Γ ! γ [ x ]) S., A .map a ⌝ ]                 ≡˘⟨ ap¡ (S.↑-⟨⟩ _ _) ⟩
    bˢ S.[ (Γ .map (Γ ! γ [ x ]) S.↑) S.∘ S.⟨ A .map a ⟩ ]         ≡⟨ S.[]-∘ _ _ _ ⟩
    bˢ S.[ Γ .map (Γ ! γ [ x ]) S.↑ ] S.[ S.⟨ A .map a ⟩ ]         ≡˘⟨ S.⇒-β _ _ ⟩
    S.app ⌜ S.lam (bˢ S.[ Γ .map (Γ ! γ [ x ]) S.↑ ]) ⌝ (A .map a) ≡˘⟨ ap¡ (S.lam-[] _ _) ⟩
    S.app (S.lam bˢ S.[ ⌜ Γ .map (Γ ! γ [ x ]) ⌝ ]) (A .map a)     ≡⟨ ap! (Γ .map-[] _ _) ⟩
    S.app ⌜ S.lam bˢ S.[ Γ .map γ S.∘ Wk-emb x ] ⌝ (A .map a)      ≡⟨ ap! (S.[]-∘ _ _ _) ⟩
    S.app (S.lam bˢ S.[ Γ .map γ ] S.[ Wk-emb x ]) (A .map a)      ∎
  lam {Γ = Γ} {bˢ = bˢ} b .![] γ x =
    Fun-path
      ( S.lam bˢ S.[ ⌜ Γ .map (Γ ! γ [ x ]) ⌝ ] ≡⟨ ap! (Γ .map-[] _ _) ⟩
        S.lam bˢ S.[ Γ .map γ S.∘ Wk-emb x ]    ≡⟨ S.[]-∘ _ _ _ ⟩
        S.lam bˢ S.[ Γ .map γ ] S.[ Wk-emb x ]  ∎)
      λ y a → ap (b .sem) (ap (P._, _) (sym (Γ .![]-∘ _ _ _)))
  lam b .map γ = refl

  lam-[] :
    (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
    lam b [ γ ] ≡ᵗ[ S.lam-[] _ _ ] lam (b [ γ ↑ ])
  lam-[] {Γ = Γ} {bˢ = bˢ} {Δ = Δ} {γˢ = γˢ} b γ = Tm-path λ δ →
    Fun-path
      ( S.lam bˢ S.[ ⌜ Γ .map (γ .sem δ) ⌝ ]   ≡⟨ ap! (γ .map _) ⟩
        S.lam bˢ S.[ γˢ S.∘ Δ .map δ ]         ≡⟨ S.[]-∘ _ _ _ ⟩
        ⌜ S.lam bˢ S.[ γˢ ] ⌝ S.[ Δ .map δ ]   ≡⟨ ap! (S.lam-[] _ _) ⟩
        S.lam (bˢ S.[ γˢ S.↑ ]) S.[ Δ .map δ ] ∎)
      λ x a → ap (b .sem) (ap (P._, _) (sym (γ .![] _ _)))

  ⇒-β :
    (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
    app (lam b) a ≡ᵗ[ S.⇒-β _ _ ] b [ ⟨ a ⟩ ]
  ⇒-β {Γ = Γ} b a = Tm-path λ γ → ap (b .sem) (ap (P._, _) (Γ .![]-id _))

  ⇒-η : (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ S.⇒-η _ ] f
  ⇒-η {Γ = Γ} {fˢ = fˢ} f = Tm-path λ γ →
    Fun-path
      ( ⌜ S.lam (S.app (fˢ S.[ S.p ]) S.q) ⌝ S.[ Γ .map γ ] ≡⟨ ap! (S.⇒-η _) ⟩
        fˢ S.[ Γ .map γ ]                                   ≡˘⟨ f .map _ ⟩
        f .sem γ .syn                                       ∎)
      λ x a →
        ⌜ f .sem (Γ ! γ [ x ]) ⌝ .sem W.id a ≡⟨ ap! (f .![] _ _) ⟩
        f .sem γ .sem ⌜ x W.∘ W.id ⌝ a       ≡⟨ ap! (W.idr _) ⟩
        f .sem γ .sem x a                    ∎

  ⊥ : Ty S.⊥
  ⊥ .sem X = el! (Nf X S.⊥)
  ⊥ ._!_[_] = _[_]ᴺᶠ
  ⊥ .![]-∘ = []ᴺᶠ-∘
  ⊥ .![]-id = []ᴺᶠ-id

  ⊥ .map = Nf-emb
  ⊥ .map-[] = Nf-emb-[]

  ⊥ .quo t = t
  ⊥ .quo-[] t x = refl
  ⊥ .emb-quo t = refl

  ⊥ .ref = N.⊥-ne
  ⊥ .ref-[] t x = refl
  ⊥ .map-ref t = refl

  ⊥-rec-sem : (A : Ty Aˢ) → Nf X S.⊥ → ∣ A .sem X ∣
  ⊥-rec-sem A (N.⊥-ne t) = A .ref (N.⊥-rec t)

  ⊥-rec : Tm Γ ⊥ tˢ → Tm Γ A (S.⊥-rec tˢ)
  ⊥-rec {A = A} t .sem γ = ⊥-rec-sem A (t .sem γ)
  ⊥-rec {Γ = Γ} {A = A} t .![] γ x =
    ⊥-rec-sem A ⌜ t .sem (Γ ! γ [ x ]) ⌝ ≡⟨ ap! (t .![] _ _) ⟩
    ⊥-rec-sem A (t .sem γ [ x ]ᴺᶠ)       ≡⟨ ⊥-rec-![] (t .sem γ) ⟩
    A ! ⊥-rec-sem A (t .sem γ) [ x ]     ∎
    where
    ⊥-rec-![] : ∀ t → ⊥-rec-sem A (t [ x ]ᴺᶠ) ≡ A ! ⊥-rec-sem A t [ x ]
    ⊥-rec-![] (N.⊥-ne x) = A .ref-[] _ _
  ⊥-rec {Γ = Γ} {tˢ = tˢ} {A = A} t .map γ =
    A .map (⊥-rec-sem A (t .sem γ)) ≡⟨ ⊥-rec-map (t .sem γ) ⟩
    S.⊥-rec ⌜ Nf-emb (t .sem γ) ⌝   ≡⟨ ap! (t .map _) ⟩
    S.⊥-rec (tˢ S.[ Γ .map γ ])     ≡˘⟨ S.⊥-rec-[] _ _ ⟩
    S.⊥-rec tˢ S.[ Γ .map γ ]       ∎
    where
    ⊥-rec-map : ∀ t → A .map (⊥-rec-sem A t) ≡ S.⊥-rec (Nf-emb t)
    ⊥-rec-map (N.⊥-ne x) = A .map-ref _

  ⊥-rec-[] :
    (t : Tm Γ ⊥ tˢ) (γ : Sub Δ Γ γˢ) →
    ⊥-rec {A = A} t [ γ ] ≡ᵗ[ S.⊥-rec-[] _ _ ] ⊥-rec (t [ γ ])
  ⊥-rec-[] t γ = Tm-path λ δ → refl

  Bool : Ty S.Bool
  Bool .sem X = el! (Nf X S.Bool)
  Bool ._!_[_] = _[_]ᴺᶠ
  Bool .![]-∘ = []ᴺᶠ-∘
  Bool .![]-id = []ᴺᶠ-id

  Bool .map = Nf-emb
  Bool .map-[] = Nf-emb-[]

  Bool .quo t = t
  Bool .quo-[] t x = refl
  Bool .emb-quo t = refl

  Bool .ref = N.Bool-ne
  Bool .ref-[] t x = refl
  Bool .map-ref t = refl

  true : Tm Γ Bool S.true
  true .sem γ = N.true
  true .![] γ x = refl
  true .map γ = sym (S.true-[] _)

  true-[] : (γ : Sub Δ Γ γˢ) → true [ γ ] ≡ᵗ[ S.true-[] _ ] true
  true-[] γ = Tm-path λ δ → refl

  false : Tm Γ Bool S.false
  false .sem γ = N.false
  false .![] γ x = refl
  false .map γ = sym (S.false-[] _)

  false-[] : (γ : Sub Δ Γ γˢ) → false [ γ ] ≡ᵗ[ S.false-[] _ ] false
  false-[] γ = Tm-path λ δ → refl

  Bool-rec-sem :
    (A : Ty Aˢ) → ∣ A .sem X ∣ → ∣ A .sem X ∣ → Nf X S.Bool → ∣ A .sem X ∣
  Bool-rec-sem A a₁ a₂ (N.Bool-ne t) =
    A .ref (N.Bool-rec (A .quo a₁) (A .quo a₂) t)
  Bool-rec-sem A a₁ a₂ N.true = a₁
  Bool-rec-sem A a₁ a₂ N.false = a₂

  Bool-rec :
    Tm Γ A a₁ˢ → Tm Γ A a₂ˢ → Tm Γ Bool tˢ → Tm Γ A (S.Bool-rec a₁ˢ a₂ˢ tˢ)
  Bool-rec {A = A} a₁ a₂ t .sem γ =
    Bool-rec-sem A (a₁ .sem γ) (a₂ .sem γ) (t .sem γ)
  Bool-rec {Γ = Γ} {A = A} a₁ a₂ t .![] γ x =
    Bool-rec-sem A ⌜ a₁ .sem (Γ ! γ [ x ]) ⌝ (a₂ .sem (Γ ! γ [ x ])) (t .sem (Γ ! γ [ x ])) ≡⟨ ap! (a₁ .![] _ _) ⟩
    Bool-rec-sem A (A ! a₁ .sem γ [ x ]) ⌜ a₂ .sem (Γ ! γ [ x ]) ⌝ (t .sem (Γ ! γ [ x ]))   ≡⟨ ap! (a₂ .![] _ _) ⟩
    Bool-rec-sem A (A ! a₁ .sem γ [ x ]) (A ! a₂ .sem γ [ x ]) ⌜ t .sem (Γ ! γ [ x ]) ⌝     ≡⟨ ap! (t .![] _ _) ⟩
    Bool-rec-sem A (A ! a₁ .sem γ [ x ]) (A ! a₂ .sem γ [ x ]) (Bool ! t .sem γ [ x ])      ≡⟨ Bool-rec-![] _ _ (t .sem γ) ⟩
    A ! Bool-rec-sem A (a₁ .sem γ) (a₂ .sem γ) (t .sem γ) [ x ]                             ∎
    where
    Bool-rec-![] :
      ∀ a₁ a₂ t →
      Bool-rec-sem A (A ! a₁ [ x ]) (A ! a₂ [ x ]) (Bool ! t [ x ]) ≡
      A ! Bool-rec-sem A a₁ a₂ t [ x ]
    Bool-rec-![] a₁ a₂ (N.Bool-ne t) =
      A .ref (N.Bool-rec ⌜ A .quo (A ! a₁ [ x ]) ⌝ (A .quo (A ! a₂ [ x ])) (t [ x ]ᴺᵉ)) ≡⟨ ap! (A .quo-[] _ _) ⟩
      A .ref (N.Bool-rec (A .quo a₁ [ x ]ᴺᶠ) ⌜ A .quo (A ! a₂ [ x ]) ⌝ (t [ x ]ᴺᵉ))     ≡⟨ ap! (A .quo-[] _ _) ⟩
      A .ref (N.Bool-rec (A .quo a₁ [ x ]ᴺᶠ) (A .quo a₂ [ x ]ᴺᶠ) (t [ x ]ᴺᵉ))           ≡⟨ A .ref-[] _ _ ⟩
      A ! A .ref (N.Bool-rec (A .quo a₁) (A .quo a₂) t) [ x ]                           ∎
    Bool-rec-![] a₁ a₂ N.true = refl
    Bool-rec-![] a₁ a₂ N.false = refl
  Bool-rec {Γ = Γ} {A = A} {a₁ˢ = a₁ˢ} {a₂ˢ = a₂ˢ} {tˢ = tˢ} a₁ a₂ t .map γ =
    A .map (Bool-rec-sem A (a₁ .sem γ) (a₂ .sem γ) (t .sem γ))                    ≡⟨ Bool-rec-map _ _ (t .sem γ) ⟩
    S.Bool-rec ⌜ A .map (a₁ .sem γ) ⌝ (A .map (a₂ .sem γ)) (Bool .map (t .sem γ)) ≡⟨ ap! (a₁ .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) ⌜ A .map (a₂ .sem γ) ⌝ (Bool .map (t .sem γ)) ≡⟨ ap! (a₂ .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) (a₂ˢ S.[ Γ .map γ ]) ⌜ Bool .map (t .sem γ) ⌝ ≡⟨ ap! (t .map _) ⟩
    S.Bool-rec (a₁ˢ S.[ Γ .map γ ]) (a₂ˢ S.[ Γ .map γ ]) (tˢ S.[ Γ .map γ ])      ≡˘⟨ S.Bool-rec-[] _ _ _ _ ⟩
    S.Bool-rec a₁ˢ a₂ˢ tˢ S.[ Γ .map γ ]                                          ∎
    where
    Bool-rec-map :
      ∀ a₁ a₂ t →
      A .map (Bool-rec-sem A a₁ a₂ t) ≡
      S.Bool-rec (A .map a₁) (A .map a₂) (Bool .map t)
    Bool-rec-map a₁ a₂ (N.Bool-ne t) =
      A .map (A .ref (Ne.Bool-rec (A .quo a₁) (A .quo a₂) t))           ≡⟨ A .map-ref _ ⟩
      S.Bool-rec ⌜ Nf-emb (A .quo a₁) ⌝ (Nf-emb (A .quo a₂)) (Ne-emb t) ≡⟨ ap! (A .emb-quo _) ⟩
      S.Bool-rec (A .map a₁) ⌜ Nf-emb (A .quo a₂) ⌝ (Ne-emb t)          ≡⟨ ap! (A .emb-quo _) ⟩
      S.Bool-rec (A .map a₁) (A .map a₂) (Ne-emb t)                     ∎
    Bool-rec-map a₁ a₂ N.true = sym (S.Bool-β₁ _ _)
    Bool-rec-map a₁ a₂ N.false = sym (S.Bool-β₂ _ _)

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

open Normalization

Normalization : Displayed
Normalization = record {Normalization}

open STLC.Induction Normalization

private variable
  Γ : S.Con
  A : S.Ty

ref-id : ∀ Γ → ∣ Con-ind Γ .sem Γ ∣
ref-id (Γ S.▸ A) =
  Con-ind Γ ! ref-id Γ [ W.id W.∘p ] P., Ty-ind A .ref (N.var W.q)
ref-id S.◆ = P.tt

map-ref-id : ∀ Γ → Con-ind Γ .map (ref-id Γ) ≡ S.id
map-ref-id (Γ S.▸ A) =
  ⌜ Con-ind Γ .map (Con-ind Γ ! ref-id Γ [ W.id Wk.∘p ]) ⌝ S., Ty-ind A .map (Ty-ind A .ref (Ne.var W.q)) ≡⟨ ap! (Con-ind Γ .map-[] (ref-id Γ) (W.id Wk.∘p)) ⟩
  ⌜ Con-ind Γ .map (ref-id Γ) ⌝ S.∘ (Wk-emb W.id S.∘ S.p) S., Ty-ind A .map (Ty-ind A .ref (Ne.var W.q))  ≡⟨ ap! (map-ref-id _) ⟩
  ⌜ S.id S.∘ (Wk-emb W.id S.∘ S.p) ⌝ S., Ty-ind A .map (Ty-ind A .ref (Ne.var W.q))                       ≡⟨ ap! (S.idl _) ⟩
  ⌜ Wk-emb W.id ⌝ S.∘ S.p S., Ty-ind A .map (Ty-ind A .ref (Ne.var W.q))                                  ≡⟨ ap! Wk-emb-id ⟩
  ⌜ S.id S.∘ S.p ⌝ S., Ty-ind A .map (Ty-ind A .ref (Ne.var W.q))                                         ≡⟨ ap! (S.idl _) ⟩
  S.p S., ⌜ Ty-ind A .map (Ty-ind A .ref (Ne.var W.q)) ⌝                                                  ≡⟨ ap! (Ty-ind A .map-ref (Ne.var W.q)) ⟩
  S.p S., S.q                                                                                             ≡⟨ S.▸-η ⟩
  S.id                                                                                                    ∎
map-ref-id S.◆ = S.◆-η

reflect : S.Tm Γ A → ∣ Ty-ind A .sem Γ ∣
reflect {Γ} a = Tm-ind a .sem (ref-id Γ)

normalize : S.Tm Γ A → Nf Γ A
normalize {A = A} a = Ty-ind A .quo (reflect a)

completeness : (a : S.Tm Γ A) → Nf-emb (normalize a) ≡ a
completeness {Γ} {A} a =
  Nf-emb (Ty-ind A .quo (Tm-ind a .sem (ref-id Γ))) ≡⟨ Ty-ind A .emb-quo _ ⟩
  Ty-ind A .map (Tm-ind a .sem (ref-id Γ))          ≡⟨ Tm-ind a .map _ ⟩
  a S.[ ⌜ Con-ind Γ .map (ref-id Γ) ⌝ ]             ≡⟨ ap! (map-ref-id _) ⟩
  a S.[ S.id ]                                      ≡⟨ S.[]-id _ ⟩
  a                                                 ∎

Var-stability : (a : Var Γ A) → reflect (Var-emb a) ≡ Ty-ind A .ref (N.var a)
Var-stability W.q = refl
Var-stability (W._[p] {Γ} {A} a) =
  Tm-ind (Var-emb a) .sem (Con-ind Γ ! ref-id Γ [ W.id W.∘p ]) ≡⟨ Tm-ind (Var-emb a) .![] _ _ ⟩
  Ty-ind A ! ⌜ reflect (Var-emb a) ⌝ [ W.id W.∘p ]             ≡⟨ ap! (Var-stability a) ⟩
  Ty-ind A ! Ty-ind A .ref (N.var a) [ W.id W.∘p ]             ≡˘⟨ Ty-ind A .ref-[] _ _ ⟩
  Ty-ind A .ref (N.var (⌜ a W.[ W.id ] ⌝ W.[p]))               ≡⟨ ap! (W.[]-id _) ⟩
  Ty-ind A .ref (N.var (a W.[p]))                              ∎

Ne-stability : (a : Ne Γ A) → reflect (Ne-emb a) ≡ Ty-ind A .ref a
Nf-stability : (a : Nf Γ A) → normalize (Nf-emb a) ≡ a

Ne-stability (N.var a) = Var-stability a
Ne-stability (N.app {B = B} f a) =
  ⌜ reflect (Ne-emb f) ⌝ .sem W.id (reflect (Nf-emb a))         ≡⟨ ap! (Ne-stability f) ⟩
  Ty-ind B .ref (N.app ⌜ f [ W.id ]ᴺᵉ ⌝ (normalize (Nf-emb a))) ≡⟨ ap! ([]ᴺᵉ-id _) ⟩
  Ty-ind B .ref (N.app f ⌜ normalize (Nf-emb a) ⌝)              ≡⟨ ap! (Nf-stability a) ⟩
  Ty-ind B .ref (N.app f a)                                     ∎
Ne-stability (N.⊥-rec {A = A} t) = ap (⊥-rec-sem (Ty-ind A)) (Ne-stability t)
Ne-stability (N.Bool-rec {A = A} a₁ a₂ t) =
  Bool-rec-sem (Ty-ind A) (reflect (Nf-emb a₁)) (reflect (Nf-emb a₂)) ⌜ reflect (Ne-emb t) ⌝ ≡⟨ ap! (Ne-stability t) ⟩
  Ty-ind A .ref (N.Bool-rec ⌜ normalize (Nf-emb a₁) ⌝ (normalize (Nf-emb a₂)) t)             ≡⟨ ap! (Nf-stability a₁) ⟩
  Ty-ind A .ref (N.Bool-rec a₁ ⌜ normalize (Nf-emb a₂) ⌝ t)                                  ≡⟨ ap! (Nf-stability a₂) ⟩
  Ty-ind A .ref (N.Bool-rec a₁ a₂ t)                                                         ∎

Nf-stability (N.lam b) = ap N.lam (Nf-stability b)
Nf-stability (N.⊥-ne t) = ap (Ty-ind S.⊥ .quo) (Ne-stability t)
Nf-stability (N.Bool-ne t) = ap (Ty-ind S.Bool .quo) (Ne-stability t)
Nf-stability N.true = refl
Nf-stability N.false = refl

Tm≃Nf : S.Tm Γ A ≃ Nf Γ A
Tm≃Nf = Iso→Equiv (normalize P., iso Nf-emb Nf-stability completeness)

Discrete-Tm : Discrete (S.Tm Γ A)
Discrete-Tm = subst Discrete (sym (ua Tm≃Nf)) Discrete-Nf
