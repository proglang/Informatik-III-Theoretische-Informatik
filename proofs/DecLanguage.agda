module DecLanguage where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; T)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)

open import DecSets as DS using (𝔓)

DecLanguage : Set → Set
DecLanguage Σ = 𝔓 (Word Σ)

module _ {Σ : Set} where

  -- set operations (pointwise Bool predicates)

  Σ⋆ : DecLanguage Σ
  Σ⋆ = DS.U

  _∩_ : DecLanguage Σ → DecLanguage Σ → DecLanguage Σ
  _∩_ = DS._∩_

  _∪_ : DecLanguage Σ → DecLanguage Σ → DecLanguage Σ
  _∪_ = DS._∪_

  ∁ : DecLanguage Σ → DecLanguage Σ
  ∁ = DS.∁

  _⊆_ : DecLanguage Σ → DecLanguage Σ → Set
  _⊆_ = DS._⊆_

  _≐_ : DecLanguage Σ → DecLanguage Σ → Set
  _≐_ = DS._≐_

  𝟙 : DecLanguage Σ
  𝟙 ε = true
  𝟙 (_ ∷ _) = false

  -- Boolean concatenation by structural recursion over all splits.
  _·_ : DecLanguage Σ → DecLanguage Σ → DecLanguage Σ
  (L₁ · L₂) ε = L₁ ε ∧ L₂ ε
  (L₁ · L₂) (a ∷ w) = (L₁ ε ∧ L₂ (a ∷ w)) ∨ (((λ u → L₁ (a ∷ u)) · L₂) w)

  _↑_ : DecLanguage Σ → ℕ → DecLanguage Σ
  L ↑ zero = 𝟙
  L ↑ suc n = L · (L ↑ n)

  -- Star as a proposition over words: existence of some finite power
  -- accepting the word.
  _∗ : DecLanguage Σ → Word Σ → Set
  (L ∗) w = ∃[ n ] T ((L ↑ n) w)

  _⁺ : DecLanguage Σ → Word Σ → Set
  (L ⁺) w = ∃[ n ] T ((L ↑ suc n) w)
