module Grammar.Example where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Unary using (_∈_)

open import Sets using (𝔓)
open import Language using (Language)

open import Grammar

module s1s0 where

  data Σ : Set where
    O I : Σ

  G₀ : CFG Σ
  G₀ = record
    { N = ⊤
    ; S = tt
    ; P = productions
    }
    where
    productions : _
    productions tt ε = ⊤
    productions tt (x ∷ ε) = ⊥
    productions tt (x ∷ x₁ ∷ ε) = ⊥
    productions tt (x ∷ x₁ ∷ x₂ ∷ ε) = ⊥
    productions tt (inj₁ x ∷ x₁ ∷ x₂ ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ O ∷ inj₁ tt ∷ inj₁ x ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ O ∷ inj₁ tt ∷ inj₂ O ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ O ∷ inj₁ tt ∷ inj₂ I ∷ inj₁ tt ∷ ε) = ⊤
    productions tt (inj₂ O ∷ inj₁ tt ∷ inj₂ I ∷ inj₂ y ∷ ε) = ⊥
    productions tt (inj₂ O ∷ inj₂ y ∷ x₂ ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ I ∷ inj₁ tt ∷ inj₁ x ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ I ∷ inj₁ tt ∷ inj₂ O ∷ inj₁ tt ∷ ε) = ⊤
    productions tt (inj₂ I ∷ inj₁ tt ∷ inj₂ O ∷ inj₂ y ∷ ε) = ⊥
    productions tt (inj₂ I ∷ inj₁ tt ∷ inj₂ I ∷ x₃ ∷ ε) = ⊥
    productions tt (inj₂ I ∷ inj₂ y ∷ x₂ ∷ x₃ ∷ ε) = ⊥
    productions tt (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅) = ⊥
