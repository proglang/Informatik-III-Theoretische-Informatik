module Sets where

open import Level using () renaming (zero to lzero; suc to lsuc)
open import Data.Product using (∃-syntax; _×_)
open import Relation.Unary using (Pred; _∈_)

𝔓 : ∀{ℓ} → Set ℓ → Set (lsuc ℓ)
𝔓 Q = Pred Q _

non-empty : ∀ {ℓ} {Q : Set ℓ} → 𝔓{ℓ} Q → Set _
non-empty R = ∃[ q ] q ∈ R

infix 5 _≠∅
_≠∅ = non-empty

-- set comprehension notation

｛｝ : ∀ {ℓ}{A : Set ℓ} → A → A
｛｝ = λ z → z

syntax ｛｝ (λ x → M) = ｛ x ∣ M ｝

-- lift function to a set

lift : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}
  → (f : A → Pred B ℓ₁) → (Pred A ℓ₁ → Pred B ℓ₁)
lift f Pa = ｛ b ∣ ∃[ a ] a ∈ Pa × b ∈ f a ｝

lift₂ : ∀ {ℓ}{ℓc} {A : Set ℓ} {C : Set ℓc} {B : Set ℓ}
  → (f : A → B → Pred C ℓ) → (Pred A ℓ → B → Pred C ℓ)
lift₂ f Pa b = ｛ c ∣ ∃[ a ] a ∈ Pa × c ∈ f a b ｝

