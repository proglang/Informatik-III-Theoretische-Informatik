module NPDA.CFL2NPDA where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Unary using (_∈_)
open import Relation.Unary using () renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import NPDA
open import Grammar
open import Grammar.DerivationHelpers
import Grammar.DerivationTree as DerivationTree
import Grammar.Leftmost-Derivation as Leftmost-Derivation

-- NPDA from grammar

module _ {Σ : Set} (𝓖 : CFG Σ) where

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
  open Generated

  left-gen : ∀ α → accepts tt α ⊆ Generates 𝓖 α 
  left-gen γ w       (tt , NPDA.⇒*-refl) = ⇒*-refl ε
  left-gen (inj₂ a ∷ γ) w (tt , NPDA.⇒*-step (NPDA.step-a {q′ = tt} {a = b} {w′} {α = ε} refl) ⇒*-cont) =
    ⇒*-++ˡ [ inj₂ a ] (left-gen γ w′ (tt , ⇒*-cont))
  left-gen (inj₁ A ∷ γ) w (tt , NPDA.⇒*-step (NPDA.step-ε {α = α} A→α) ⇒*-cont) =
    Derivation.⇒*-step (ε , A , α , γ , refl , A→α , refl)
                       (left-gen (α ++ γ) w (tt , ⇒*-cont))

  run-forest-cont :
    ∀ {α u} →
    DerivationTree.Forest 𝓖 α u →
    ∀ {γ v} →
    (tt , v , γ) ⇒* (tt , ε , ε) →
    (tt , u ++ v , α ++ γ) ⇒* (tt , ε , ε)
  run-forest-cont DerivationTree.empty cont = cont
  run-forest-cont (DerivationTree.term {a = a} {α = α} {w = u} forest) {γ} {v} cont =
    NPDA.⇒*-step
      (NPDA.step-a {q = tt} {q′ = tt} {a = a} {w = u ++ v} {Z = inj₂ a} {α = ε} {γ = α ++ γ} refl)
      (run-forest-cont forest {γ = γ} {v = v} cont)
  run-forest-cont (DerivationTree.nonterm {A = A} {α = α} {u = u} {v = v} (DerivationTree.node {rhs = rhs} rhs∈PA forest-rhs) forest-tail) {γ} {z} cont =
    NPDA.⇒*-step
      (NPDA.step-ε {q = tt} {q′ = tt} {w = (u ++ v) ++ z} {Z = inj₁ A} {α = rhs} {γ = α ++ γ} rhs∈PA)
      (subst
        (λ input → (tt , input , rhs ++ (α ++ γ)) ⇒* (tt , ε , ε))
        (sym (++-assoc u v z))
        (run-forest-cont forest-rhs {γ = α ++ γ} {v = v ++ z}
          (run-forest-cont forest-tail {γ = γ} {v = z} cont)))

  run-forest :
    ∀ {α w} →
    DerivationTree.Forest 𝓖 α w →
    (tt , w , α) ⇒* (tt , ε , ε)
  run-forest {α} {w} forest =
    subst
      (λ stack → (tt , w , stack) ⇒* (tt , ε , ε))
      (++-identityʳ α)
      (subst
        (λ input → (tt , input , α ++ ε) ⇒* (tt , ε , ε))
        (++-identityʳ w)
        (run-forest-cont forest {γ = ε} {v = ε} NPDA.⇒*-refl))

  -- for this direction it is preferable to have a leftmost derivation or a derivation tree
  right-gen : ∀ α → Generates 𝓖 α ⊆ accepts tt α
  right-gen α w deriv =
    tt , run-forest
      (DerivationTree.leftmost⇒forest 𝓖
        (Leftmost-Derivation.normalize 𝓖 α w deriv))

  correct : NPDA.Lang 𝓚 ≐ Generated.Lang 𝓖
  correct = left-gen [ inj₁ S ] , right-gen [ inj₁ S ]
