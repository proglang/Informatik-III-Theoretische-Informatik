module Sets where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; _^_)
open import Data.Fin using (Fin)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred; _∈_)

variable
  ℓ₁ ℓ₂ : Level

record Iso (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    fwd : A → B
    bwd : B → A
    fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
    bwd∘fwd : ∀ a → bwd (fwd a) ≡ a

Finite : ∀ {ℓ} → Set ℓ → Set ℓ
Finite X = ∃[ n ] Iso X (Fin n)

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

-- properties

-- Finite-𝔓 : ∀ {ℓ} {X : Set ℓ} → Finite X → Finite (𝔓 X)
-- Finite-𝔓 (n , iso) = (2 ^ n) , {!!}
