module NPDA.CFL2NPDA where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Unary using (_∈_)
open import Relation.Unary using () renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import NPDA
open import Grammar
open import Grammar.DerivationHelpers

-- grammar from NPDA

module Construction {Σ : Set} (𝓖 : CFG Σ) where

  open CFG 𝓖 

  𝓚 : NPDA Σ
  𝓚 = record
    { Q = ⊤
    ; Γ = N ⊎ Σ 
    ; qinit = tt
    ; Zinit =  inj₁ S
    ; δ = δ-map
    }
    where
      δ-map : _
      δ-map tt (just a) (inj₁ A) x₃ = ⊥
      δ-map tt (just a) (inj₂ b) (tt , ε) = a ≡ b
      δ-map tt (just a) (inj₂ y) (tt , x ∷ snd) = ⊥
      δ-map tt nothing (inj₁ A) (tt , γ) = γ ∈ P A
      δ-map tt nothing (inj₂ b) x₃ = ⊥

  open NPDA.NPDA 𝓚
  open Derivation 𝓖 renaming (_⇒*_ to _⊢*_)
  open For 𝓖 using (⇒*-++ˡ)

  left-gen : ∀ α w → ⊤ × (tt , w , α) ⇒* (tt , ε , ε) → α ⊢* map inj₂ w
  left-gen γ w       (tt , NPDA.⇒*-refl) = ⇒*-refl ε
  left-gen (inj₂ a ∷ γ) w (tt , NPDA.⇒*-step (NPDA.step-a {q′ = tt} {a = b} {w′} {α = ε} refl) ⇒*-cont) =
    ⇒*-++ˡ [ inj₂ a ] (left-gen γ w′ (tt , ⇒*-cont))
  left-gen (inj₁ A ∷ γ) w (tt , NPDA.⇒*-step (NPDA.step-ε {α = α} A→α) ⇒*-cont) =
    Derivation.⇒*-step (ε , A , α , γ , refl , A→α , refl)
                       (left-gen (α ++ γ) w (tt , ⇒*-cont))

  -- for this direction it is preferable to have a leftmost derivation or a derivation tree
  right-gen : ∀ α w → α ⊢* map inj₂ w → ⊤ × (tt , w , α) ⇒* (tt , ε , ε)
  right-gen α w x = {!!}

  correct : NPDA.Lang 𝓚 ≐ Generated.Lang 𝓖
  correct = left-gen [ inj₁ S ] , right-gen [ inj₁ S ]
