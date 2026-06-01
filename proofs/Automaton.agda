module Automaton where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_)

open import Language
open import Isomorphism using (Iso; _↔_)


-- automaton

record Automaton (Σ : Set) : Set (lsuc ℓ) where
  field
    Q : Set ℓ
    δ : Q → Σ → Q
    qinit : Q
    F : Q → Set

  δ̃ : Q → Word Σ → Q
  δ̃ q ε = q
  δ̃ q (x ∷ w) = δ̃ (δ q x) w

  accepts : Q → Language Σ
  accepts q w = δ̃ q w ∈ F

  Lang : Language Σ
  Lang = accepts qinit

  reachable : Q → Set _
  reachable q = ∃[ w ] δ̃ qinit w ≡ q

