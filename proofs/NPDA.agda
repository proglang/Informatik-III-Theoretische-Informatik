module NPDA where

open import Data.List using (_∷_; _++_; [_]; length) renaming (List to Word; [] to ε)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Unary using (Pred; _∈_; _∉_; _∩_; _∪_; Empty; ∅; ｛_｝)
  renaming (_⊆_ to _⊆′_; _≐_ to _≐′_)
open import Relation.Unary using () renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)

open import Language
open import Isomorphism using (Iso)
open import Finiteness using (Finite)
open import Sets

-- nondeterministic pushdown automaton

record NPDA (Σ : Set) : Set₁ where
  field
    Q      : Set                -- states
    Γ      : Set                -- stack alphabet
    qinit  : Q                  -- initial state
    Zinit  : Γ                  -- stack bottom symbol
    δ      : Q → Maybe Σ → Γ → 𝔓 (Q × Word Γ)

  Conf : Set
  Conf = Q × Word Σ × Word Γ

  data _⇒_ : Conf → Conf → Set where

    step-a : ∀ {q q′} {a} {w} {Z} {α} {γ}
      → (q′ , α) ∈ δ q (just a) Z
      → (q , a ∷ w , Z ∷ γ) ⇒ (q′ , w , α ++ γ)

    step-ε : ∀ {q q′} {w} {Z} {α} {γ}
      → (q′ , α) ∈ δ q nothing Z
      → (q , w , Z ∷ γ) ⇒ (q′ , w , α ++ γ)
    
  data _⇒*_ : Conf → Conf → Set where

    ⇒*-refl : ∀ {C} → C ⇒* C

    ⇒*-step : ∀ {C₁ C₂ C₃}
      → C₁ ⇒ C₂ → C₂ ⇒* C₃
      → C₁ ⇒* C₃

  accepts-at : Q → Word Γ → Q → Language Σ
  accepts-at q γ q′ = ｛ w ∣ (q , w , γ) ⇒* (q′ , ε , ε) ｝

  accepts : Q → Word Γ → Language Σ
  accepts q γ = ｛ w ∣ ∃[ q′ ] accepts-at q γ q′ w ｝

  Lang : Language Σ
  Lang = accepts qinit [ Zinit ]

  2bounded : Set
  2bounded = ∀ q x Z q′ γ → (q′ , γ) ∈ δ q x Z → length γ ≤ 2

  -- experimental; probably useless

  step : Conf → 𝔓 Conf
  step (q , w , ε) = ∅
  step (q , w , Z ∷ γ) = ｛ (q′ , w′ , γ′ ) ∣ (∃[ α ] (q′ , α) ∈ δ q nothing Z × w ≡ w′ × γ′ ≡ α ++ γ ) ｝
                       ∪ ｛ (q′ , w′ , γ′ ) ∣ (∃[ α ] ∃[ a ] (q′ , α) ∈ δ q (just a) Z × w ≡ a ∷ w′ × γ′ ≡ α ++ γ ) ｝

  step-sound : ∀ C C′ → C′ ∈ step C → C ⇒ C′
  step-sound (q , w , Z ∷ γ) (q′ , w′ , γ′) (inj₁ (α , q′α∈δqεZ , refl , refl)) = step-ε q′α∈δqεZ
  step-sound (q , a ∷ w , Z ∷ γ) (q′ , w′ , γ′) (inj₂ (α , b , q′α∈δqaZ , refl , refl)) = step-a q′α∈δqaZ

  step-complete : ∀ C C′ → C ⇒ C′ → C′ ∈ step C
  step-complete (q , w , Z ∷ γ) C′ (step-ε q′α∈δqεZ) = inj₁ (_ , q′α∈δqεZ , refl , refl)
  step-complete (q , a ∷ w , Z ∷ γ) C′ (step-a q′α∈δqaZ) = inj₂ (_ , a , (q′α∈δqaZ , refl , refl))
