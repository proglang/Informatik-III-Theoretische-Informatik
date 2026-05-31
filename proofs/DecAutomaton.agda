module DecAutomaton where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; T)
open import Data.List using (_∷_) renaming (List to Word; [] to ε)
open import Data.Product using (∃-syntax; _×_; _,_; swap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DecSets using (𝔓)
open import DecLanguage using (DecLanguage)

variable
  ℓ : Level

_↔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
A ↔ B = (A → B) × (B → A)

record Automaton (Σ : Set) : Set₁ where
  field
    Q : Set
    δ : Q → Σ → Q
    qinit : Q
    F : 𝔓 Q

  δ̃ : Q → Word Σ → Q
  δ̃ q ε = q
  δ̃ q (x ∷ w) = δ̃ (δ q x) w

  acceptsᵇ : Q → DecLanguage Σ
  acceptsᵇ q w = F (δ̃ q w)

  accepts : Q → Word Σ → Set
  accepts q w = T (acceptsᵇ q w)

  Langᵇ : DecLanguage Σ
  Langᵇ = acceptsᵇ qinit

  Lang : Word Σ → Set
  Lang = accepts qinit

  reachable : Q → Set _
  reachable q = ∃[ w ] δ̃ qinit w ≡ q

  _≈_ : Q → Q → Set
  p ≈ q = ∀ w → accepts p w ↔ accepts q w

module _ {Σ} (A : Automaton Σ) where
  open Automaton A

  -- ≈ is equivalence
  ≈-refl : ∀ {q} → q ≈ q
  ≈-refl w = (λ z → z) , (λ z → z)

  ≈-refl-eq : ∀ {p q} → p ≡ q → p ≈ q
  ≈-refl-eq refl = ≈-refl

  ≈-sym : ∀ {q p} → p ≈ q → q ≈ p
  ≈-sym p≈q w = swap (p≈q w)

  ≈-trans : ∀ {p q r} → p ≈ q → q ≈ r → p ≈ r
  ≈-trans p≈q q≈r w with p≈q w | q≈r w
  ... | pq₁ , pq₂ | qr₁ , qr₂ = (λ z → qr₁ (pq₁ z)) , (λ z → pq₂ (qr₂ z))

  -- ≈ is compatible
  ≈-compatible : ∀ {p q} {x} → p ≈ q → δ p x ≈ δ q x
  ≈-compatible {x = x} p≈q w = p≈q (x ∷ w)
