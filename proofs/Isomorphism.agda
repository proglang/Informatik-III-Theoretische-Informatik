module Isomorphism where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import Function using (_∘_)

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level


-- biimplication

_↔_ : ∀ {ℓ₁ ℓ₂} →  Set ℓ₁ → Set ℓ₂ → Set _
A ↔ B = (A → B) × (B → A)


record Iso (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    fwd : A → B
    bwd : B → A
    fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
    bwd∘fwd : ∀ a → bwd (fwd a) ≡ a

comp : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → Iso A B → Iso B C → Iso A C
comp iso-ab iso-bc =
  record
    { fwd = Iso.fwd iso-bc ∘ Iso.fwd iso-ab
    ; bwd = Iso.bwd iso-ab ∘ Iso.bwd iso-bc
    ; fwd∘bwd = λ c →
        trans
          (cong (Iso.fwd iso-bc) (Iso.fwd∘bwd iso-ab (Iso.bwd iso-bc c)))
          (Iso.fwd∘bwd iso-bc c)
    ; bwd∘fwd = λ a →
        trans
          (cong (Iso.bwd iso-ab) (Iso.bwd∘fwd iso-bc (Iso.fwd iso-ab a)))
          (Iso.bwd∘fwd iso-ab a)
    }

inverse-iso : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → Iso A B → Iso B A
inverse-iso iso =
  record
    { fwd = Iso.bwd iso
    ; bwd = Iso.fwd iso
    ; fwd∘bwd = Iso.bwd∘fwd iso
    ; bwd∘fwd = Iso.fwd∘bwd iso
    }


record PropIso ℓ : Set (lsuc ℓ) where
  field
    fwd : Set ℓ → Set ℓ
    bwd : Set ℓ → Set ℓ
    fwd∘bwd : ∀ b → fwd (bwd b) ↔ b
    bwd∘fwd : ∀ a → bwd (fwd a) ↔ a
