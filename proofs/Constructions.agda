module Constructions where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂; <_,_>) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_; _∩_; _∪_; ∁)
  renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)

open import Language
open import Automaton as BaseAutomaton

module _ {Σ} where
--  open Automaton

  -- product construction: intersection

  intersection : Automaton {ℓ} Σ → Automaton {ℓ} Σ → Automaton Σ
  intersection A₁ A₂ = record {
    Q      = Q₁ × Q₂ ;
    δ      = λ{(q₁ , q₂) a → δ₁ q₁ a , δ₂ q₂ a} ;
    qinit  = qinit₁ , qinit₂ ;
    F      = λ{(FA , FB) → F₁ FA × F₂ FB}
    }
    where
      open Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁ ; F to F₁)
      open Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂ ; F to F₂)

  module Intersection (A B : Automaton{ℓ} Σ) where
    open Automaton
    open Automaton A renaming (Q to Q₁; δ to δA) hiding (accepts; Lang)
    open Automaton B renaming (Q to Q₂; δ to δB) hiding (accepts; Lang)

    intersection-left : (q₁ : Q₁) (q₂ : Q₂)
      → accepts (intersection A B) (q₁ , q₂) ⊆ (accepts A q₁ ∩ accepts B q₂)
    intersection-left q₁ q₂ ε ε∈ = ε∈
    intersection-left q₁ q₂ (a ∷ w) aw∈ = intersection-left (δA q₁ a) (δB q₂ a) w aw∈

    intersection-right : (q₁ : Q₁) (q₂ : Q₂)
      → (accepts A q₁ ∩ accepts B q₂) ⊆ accepts (intersection A B) (q₁ , q₂)
    intersection-right q₁ q₂ ε ε∈ = ε∈
    intersection-right q₁ q₂ (a ∷ w) aw∈ = intersection-right (δA q₁ a) (δB q₂ a) w aw∈

    correct : Lang (intersection A B) ≐ (Lang A ∩ Lang B)
    correct = intersection-left (qinit A) (qinit B) , intersection-right (qinit A) (qinit B)

  -- product construction: union

  union : Automaton{ℓ} Σ → Automaton{ℓ} Σ → Automaton Σ
  union A₁ A₂ = record {
    Q      = Q₁ × Q₂ ;
    δ      = λ{(q₁ , q₂) a → δ₁ q₁ a , δ₂ q₂ a} ;
    qinit  = qinit₁ , qinit₂ ;
    F      = λ{(FA , FB) → F₁ FA ⊎ F₂ FB}
    }
    where
      open Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁ ; F to F₁)
      open Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂ ; F to F₂)


  module Union (A₁ A₂ : Automaton{ℓ} Σ) where
    open Automaton (union A₁ A₂)
    open Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; accepts to accepts₁; Lang to Lang₁)
    open Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; accepts to accepts₂; Lang to Lang₂)

    union-left : (q₁ : Q₁) (q₂ : Q₂) → accepts (q₁ , q₂) ⊆ (accepts₁ q₁ ∪ accepts₂ q₂)
    union-left q₁ q₂ ε ε∈ = ε∈
    union-left q₁ q₂ (a ∷ w) aw∈ = union-left (δ₁ q₁ a) (δ₂ q₂ a) w aw∈

    union-right : (q₁ : Q₁) (q₂ : Q₂) → (accepts₁ q₁ ∪ accepts₂ q₂) ⊆ accepts (q₁ , q₂)
    union-right q₁ q₂ ε ε∈ = ε∈
    union-right q₁ q₂ (a ∷ w) aw∈ = union-right (δ₁ q₁ a) (δ₂ q₂ a) w aw∈

    correct : Lang ≐ (Lang₁ ∪ Lang₂)
    correct = union-left qinit₁ qinit₂ , union-right qinit₁ qinit₂

  -- complement

  open Automaton
  complement : Automaton{ℓ} Σ → Automaton Σ
  complement A = record { Q = Q A ; δ = δ A ; qinit = qinit A ; F = λ x → ¬ F A x }

  module Complement (A : Automaton{ℓ} Σ) where
    open Automaton A renaming (Q to Q₁; δ to δ₁) hiding (accepts)

    complement-left : (q₁ : Q₁)
      → accepts (complement A) q₁ ⊆ ∁ (accepts A q₁)
    complement-left q₁ ε ε∉ ε∈ = contradiction ε∈ ε∉
    complement-left q₁ (a ∷ w) aw∉ aw∈ = complement-left (δ₁ q₁ a) w aw∉ aw∈

    complement-right : (q₁ : Q₁)
      → ∁ (accepts A q₁) ⊆ accepts (complement A) q₁
    complement-right q₁ ε ε∉ = ε∉
    complement-right q₁ (a ∷ w) aw∉ = complement-right (δ₁ q₁ a) w aw∉

  complement-correct :
    (A : Automaton{ℓ} Σ)
    → Lang (complement A) ≐ ∁ (Lang A)
  complement-correct A = Complement.complement-left A (qinit A) , Complement.complement-right A (qinit A)
