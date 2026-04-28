module FiniteAutomaton where

open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; contradiction)


open import Language


record FiniteAutomaton (Σ : Set) : Set where
  field
    {n} : ℕ

  Q : Set
  Q = Fin n

  field
    δ : Q → Σ → Q
    qinit : Q
    F : Subset n


module _ {Σ} (A : FiniteAutomaton Σ) where
  open FiniteAutomaton A

  δ̃ : Q → Word Σ → Q
  δ̃ q ε = q
  δ̃ q (x ∷ w) = δ̃ (δ q x) w

  accepts : Q → Language Σ
  accepts q w = δ̃ q w ∈ F

  Lang : Language Σ
  Lang = accepts qinit

  reachable : Q → Set _
  reachable q = ∃[ w ] δ̃ qinit w ≡ q

  _≈_ : Q → Q → Set
  p ≈ q = ∀ w → (δ̃ p w ∈ F) ↔ (δ̃ q w ∈ F)

  -- ≈ is equivalence
  ≈-refl : ∀ {q} → q ≈ q
  ≈-refl w = (λ z → z) , (λ z → z)

  ≈-sym : ∀ {q p} → p ≈ q → q ≈ p
  ≈-sym p≈q w = swap (p≈q w)

  ≈-trans : ∀ {p q r} → p ≈ q → q ≈ r → p ≈ r
  ≈-trans p≈q q≈r w with p≈q w | q≈r w
  ... | pq₁ , pq₂ | qr₁ , qr₂ = (λ z → qr₁ (pq₁ z)) , (λ z → pq₂ (qr₂ z))

  -- ≈ is compatible
  ≈-compatible : ∀ {p q} {x} → p ≈ q → δ p x ≈ δ q x
  ≈-compatible {x = x} p≈q w = p≈q (x ∷ w)

  -- equivalence classes
  
  ≈-class : (X : Subset n) → Set
  ≈-class X = ∃[ p ] p ∈ X × ∀ q → (q ∈ X) ↔ (p ≈ q)
  
  -- equivalence class of a state p

  [_]≈ : Q → Subset n
  [ p ]≈ = {!!}

  is-≈-class : ∀ p → ≈-class ([ p ]≈)
  is-≈-class p₀ = p₀ , {!!}
