module ND-Automaton where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (Pred; _∈_; _∉_;_∩_; Empty; ｛_｝) renaming (_⊆_ to _⊆′_)

open import Language hiding (_∩_)

import Automaton as DET

-- auxiliary definitions for sets

𝔓 : Set → Set₁
𝔓 Q = Pred Q lzero

non-empty : {Q : Set} → 𝔓 Q → Set
non-empty R = ∃[ q ] q ∈ R

infix 5 _≠∅
_≠∅ = non-empty

-- set comprehension notation

｛｝ : ∀ {ℓ}{A : Set ℓ} → A → A
｛｝ = λ z → z

syntax ｛｝ (λ x → M) = ｛ x ∣ M ｝

-- nondeterministic automaton

record ND-Automaton (Σ : Set) : Set₁ where
  field
    Q      : Set
    δ      : Q → Σ → 𝔓 Q
    qinit  : Q
    F      : 𝔓 Q

  δ̃ : Q → Word Σ → 𝔓 Q
  δ̃ q ε        = ｛ q ｝
  δ̃ q (a ∷ w)  = ｛ p ∣ ∃[ q′ ] q′ ∈ δ q a × p ∈ δ̃ q′ w ｝

  accepts : Q → Language Σ
  accepts q w = F ∩ δ̃ q w ≠∅

  Lang : Language Σ
  Lang = accepts qinit

  reachable : 𝔓 Q
  reachable q = ∃[ w ] q ∈ δ̃ qinit w

-- powerset construction

module _ {Σ : Set} where
  powerset : ND-Automaton Σ → DET.Automaton Σ
  powerset 𝓝 = record {
    Q      =  𝔓 Qₙ ;
    δ      =  λ qq a → ｛ p ∣ ∃[ q ] q ∈ qq × p ∈ δₙ q a ｝ ;
    qinit  =  ｛ qinitₙ ｝ ;
    F      =  λ qq → Fₙ ∩ qq ≠∅
    }
    where open ND-Automaton 𝓝 renaming (Q to Qₙ; δ to δₙ; qinit to qinitₙ; F to Fₙ)

-- correctness proof of powerset construction

module Powerset {Σ : Set} (𝓝 :  ND-Automaton Σ) where
  open ND-Automaton 𝓝
  open DET.Automaton (powerset 𝓝) renaming (Q to Qₚ; δ to δₚ; δ̃ to δ̃ₚ; qinit to qinitₚ; accepts to acceptsₚ)

  -- monotonicity of δ

  δ-mono : (q1 q2 : Qₚ) → q1 ⊆′ q2 → ∀ a → δₚ q1 a ⊆′ δₚ q2 a
  δ-mono q1 q2 q1⊆q2 a (q , q∈q1 , x∈δ-q-a) = q , (q1⊆q2 q∈q1) , x∈δ-q-a

  δ̃-mono : (q1 q2 : Qₚ) → q1 ⊆′ q2 → ∀ w → δ̃ₚ q1 w ⊆′ δ̃ₚ q2 w
  δ̃-mono q1 q2 q1⊆q2 ε = q1⊆q2
  δ̃-mono q1 q2 q1⊆q2 (a ∷ w) x∈ = δ̃-mono (λ p → ∃[ q ] q ∈ q1 × p ∈ δ q a)
                                         (λ p → ∃[ q ] q ∈ q2 × p ∈ δ q a)
                                         (δ-mono q1 q2 q1⊆q2 a) w x∈

  power-left : (qn : Q) → (qd : Qₚ) → qn ∈ qd
    → accepts qn ⊆ acceptsₚ qd
  power-left qn qd qn∈qd ε (qf , qf∈F , refl) = qf , qf∈F , qn∈qd
  power-left qn qd qn∈qd (a ∷ w) (qf , qf∈F , (q′ , q′∈δ-qn-a , qf∈δ̃-q′-w))
    with power-left q′ (δ qn a) q′∈δ-qn-a w (qf , qf∈F , qf∈δ̃-q′-w)
  ... | qf' , qf'∈F , ih = qf' , qf'∈F , δ̃-mono (δ qn a) (λ p → ∃[ q ] q ∈ qd × p ∈ δ q a) (λ {x} z → qn , qn∈qd , z) w ih

  power-right : (qd : Qₚ)
    → ∀ w → acceptsₚ qd w → ∃[ qn ] qn ∈ qd × accepts qn w
  power-right qd ε (qf , qf∈F , qf∈dq) = qf , (qf∈dq , (qf , qf∈F , refl))
  power-right qd (a ∷ w) (qf , qf∈F , qf∈δ̃)
    with power-right (δₚ qd a) w ( qf , qf∈F , qf∈δ̃)
  ... | qi , (q0 , q0∈qd , qi∈δ-q-a) , (qf0 , qf0∈F , qf0∈δ̃-qi-w) = q0 , q0∈qd , qf0 , qf0∈F , (qi , qi∈δ-q-a , qf0∈δ̃-qi-w)

  correct : ND-Automaton.Lang 𝓝 ≐ DET.Automaton.Lang (powerset 𝓝)
  correct = power-left qinit qinitₚ refl
          , λ w x → case (power-right qinitₚ w x) of λ where
                      (q0 , refl , acc-q0-w) → acc-q0-w
