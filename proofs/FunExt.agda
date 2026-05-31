module FunExt where

open import Level using ()
open import Relation.Binary.PropositionalEquality using (_≡_)


postulate
  funext : ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
    → ∀ {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
