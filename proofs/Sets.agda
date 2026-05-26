module Sets where

open import Level using () renaming (zero to lzero)
open import Data.Product using (∃-syntax; _×_)
open import Relation.Unary using (Pred; _∈_)

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

-- lift function to a set

lift : ∀ {A B} → (f : A → 𝔓 B) → (𝔓 A → 𝔓 B)
lift f Pa = ｛ b ∣ ∃[ a ] a ∈ Pa × b ∈ f a ｝

lift₂ : ∀ {ℓ} {A C} {B : Set ℓ} → (f : A → B → 𝔓 C) → (𝔓 A → B → 𝔓 C)
lift₂ f Pa b = ｛ c ∣ ∃[ a ] a ∈ Pa × c ∈ f a b ｝

