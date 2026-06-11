module Constructions where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_; _∩_; _∪_; ∁)
  renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)

open import Isomorphism using (_↔_)
open import Sets using (∀-distrib-×; ｛｝)
open import Language
open import Automaton as BaseAutomaton

module _ {Σ} where

  -- product construction: intersection

  module Product (A₁ A₂ : Automaton{ℓ} Σ) where
    open Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁; accepts to accepts₁; Lang to Lang₁)
    open Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; F to F₂; accepts to accepts₂; Lang to Lang₂)

    A∩ : Automaton Σ
    A∩ = record {
      Q      = Q₁ × Q₂ ;
      δ      = λ{(q₁ , q₂) a → δ₁ q₁ a , δ₂ q₂ a} ;
      qinit  = qinit₁ , qinit₂ ;
      F      = ｛ ( q₁ , q₂ ) ∣ q₁ ∈ F₁ × q₂ ∈ F₂ ｝
      }

    module Intersection where
      open Automaton A∩

      left-right : (q₁ : Q₁) (q₂ : Q₂) → ∀ w → accepts (q₁ , q₂) w ↔ (accepts₁ q₁ w × accepts₂ q₂ w)
      left-right q₁ q₂ ε = (λ z → z) , (λ z → z)
      left-right q₁ q₂ (a ∷ w) = left-right (δ₁ q₁ a) (δ₂ q₂ a) w

      correct : Lang ≐ (Lang₁ ∩ Lang₂)
      correct = ∀-distrib-× (left-right qinit₁ qinit₂)

    A∪ : Automaton Σ
    A∪ = record {
      Q      = Q₁ × Q₂ ;
      δ      = λ{(q₁ , q₂) a → δ₁ q₁ a , δ₂ q₂ a} ;
      qinit  = qinit₁ , qinit₂ ;
      F      = ｛ (q₁ , q₂) ∣ q₁ ∈ F₁ ⊎ q₂ ∈ F₂ ｝
      }

    module Union where
      open Automaton A∪

      left-right : (q₁ : Q₁) (q₂ : Q₂) → ∀ w → accepts (q₁ , q₂) w ↔ (accepts₁ q₁ w ⊎ accepts₂ q₂ w)
      left-right q₁ q₂ ε = (λ ε∈ → ε∈) , (λ ε∈ → ε∈)
      left-right q₁ q₂ (a ∷ w) = left-right (δ₁ q₁ a) (δ₂ q₂ a) w

      correct : Lang ≐ (Lang₁ ∪ Lang₂)
      correct = ∀-distrib-× (left-right qinit₁ qinit₂)

  -- complement

  module Complement (A : Automaton{ℓ} Σ) where
    open Automaton
    open Automaton A renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁; Lang to Lang₁; accepts to accepts₁)

    ∁A : Automaton Σ
    ∁A = record {
      Q = Q₁ ;
      δ = δ₁ ;
      qinit = qinit₁ ;
      F = ∁ F₁
      }

    left-right : (q₁ : Q₁) → ∀ w → (accepts ∁A q₁ w) ↔ (¬ accepts₁ q₁ w)
    left-right q₁ ε = (λ z → z) , (λ z → z)
    left-right q₁ (a ∷ w) = left-right (δ₁ q₁ a) w

    correct : Lang ∁A ≐ ∁ Lang₁
    correct = ∀-distrib-× (left-right qinit₁)
