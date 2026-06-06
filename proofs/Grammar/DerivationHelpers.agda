module Grammar.DerivationHelpers where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; _++_; map; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Unary using (_∈_)

open import Grammar

module For {Σ : Set} (G : CFG Σ) where
  open CFG G using (N; P; Symbol; _⇒_; _⇒ˡ_; Sentential)
  open Derivation G using (_⇒*_; ⇒*-refl; ⇒*-step)

  terminals : Word Σ → Sentential
  terminals = Grammar.terminals CFG-instance G

  terminals-++ : ∀ u v → terminals u ++ terminals v ≡ terminals (u ++ v)
  terminals-++ u v = sym (map-++ inj₂ u v)

  step-++ʳ : ∀ {α β} γ → α ⇒ β → (α ++ γ) ⇒ (β ++ γ)
  step-++ʳ γ (u , A , y , v , eq-in , y∈PA , eq-out) =
    u , A , y , v ++ γ
    , trans (cong (_++ γ) eq-in) (++-assoc u (inj₁ A ∷ v) γ)
    , y∈PA
    , trans (cong (_++ γ) eq-out)
        (trans (++-assoc u (y ++ v) γ)
          (cong (u ++_) (++-assoc y v γ)))

  step-++ˡ : ∀ α {β γ} → β ⇒ γ → (α ++ β) ⇒ (α ++ γ)
  step-++ˡ α (u , A , y , v , eq-in , y∈PA , eq-out) =
    α ++ u , A , y , v
    , trans (cong (α ++_) eq-in) (sym (++-assoc α u (inj₁ A ∷ v)))
    , y∈PA
    , trans (cong (α ++_) eq-out) (sym (++-assoc α u (y ++ v)))

  ⇒*-trans : ∀ {α β γ} → α ⇒* β → β ⇒* γ → α ⇒* γ
  ⇒*-trans (⇒*-refl α) β⇒*γ = β⇒*γ
  ⇒*-trans (⇒*-step α⇒β β⇒*γ) γ⇒*δ =
    ⇒*-step α⇒β (⇒*-trans β⇒*γ γ⇒*δ)

  ⇒*-++ʳ : ∀ {α β} γ → α ⇒* β → (α ++ γ) ⇒* (β ++ γ)
  ⇒*-++ʳ γ (⇒*-refl α) = ⇒*-refl (α ++ γ)
  ⇒*-++ʳ γ (⇒*-step α⇒β β⇒*γ) =
    ⇒*-step (step-++ʳ γ α⇒β) (⇒*-++ʳ γ β⇒*γ)

  ⇒*-++ˡ : ∀ α {β γ} → β ⇒* γ → (α ++ β) ⇒* (α ++ γ)
  ⇒*-++ˡ α (⇒*-refl β) = ⇒*-refl (α ++ β)
  ⇒*-++ˡ α (⇒*-step β⇒γ γ⇒*δ) =
    ⇒*-step (step-++ˡ α β⇒γ) (⇒*-++ˡ α γ⇒*δ)

  production-step : ∀ {A rhs} → rhs ∈ P A → [ inj₁ A ] ⇒ rhs
  production-step {A = A} {rhs = rhs} rhs∈P =
    ε , A , rhs , ε , refl , rhs∈P , sym (++-identityʳ rhs)

  no-stepˡ-ε : ∀ β → ε ⇒ˡ β → ⊥
  no-stepˡ-ε β (ε , A , y , v , () , y∈PA , eq-out)
  no-stepˡ-ε β (x ∷ u , A , y , v , () , y∈PA , eq-out)

  terminal-stepˡ-tail : ∀ a α β → (inj₂ a ∷ α) ⇒ˡ β → ∃[ β′ ] β ≡ inj₂ a ∷ β′ × α ⇒ˡ β′
  terminal-stepˡ-tail a α β (ε , A , y , v , () , y∈PA , eq-out)
  terminal-stepˡ-tail a .(map inj₂ u ++ inj₁ A ∷ v) .(inj₂ a ∷ map inj₂ u ++ y ++ v)
    (a ∷ u , A , y , v , refl , y∈PA , refl) =
    map inj₂ u ++ y ++ v , refl , u , A , y , v , refl , y∈PA , refl

  leftmost-head-inversion : ∀ A α β → (inj₁ A ∷ α) ⇒ˡ β → ∃[ rhs ] rhs ∈ P A × β ≡ rhs ++ α
  leftmost-head-inversion A α β (ε , .A , rhs , .α , refl , rhs∈PA , eq-out) =
    rhs , rhs∈PA , eq-out
  leftmost-head-inversion A α β (x ∷ u , B , rhs , v , () , rhs∈PB , eq-out)

  single-leftmost-step-inversion : ∀ A β → [ inj₁ A ] ⇒ˡ β → ∃[ rhs ] rhs ∈ P A × β ≡ rhs
  single-leftmost-step-inversion A β step
    with leftmost-head-inversion A ε β step
  ... | rhs , rhs∈PA , β≡rhs++ε =
    rhs , rhs∈PA , trans β≡rhs++ε (++-identityʳ rhs)

  nonterminal-prefix≢terminals : ∀ A α w → inj₁ A ∷ α ≢ terminals w
  nonterminal-prefix≢terminals A α ε ()
  nonterminal-prefix≢terminals A α (a ∷ w) ()

  combine-term : ∀ {α β} u v → α ⇒* terminals u → β ⇒* terminals v → α ++ β ⇒* terminals (u ++ v)
  combine-term {α} {β} u v α⇒*u β⇒*v =
    subst (λ γ → α ++ β ⇒* γ) (terminals-++ u v)
      (⇒*-trans (⇒*-++ʳ β α⇒*u) (⇒*-++ˡ (terminals u) β⇒*v))
