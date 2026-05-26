module Constructions where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
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
  open Automaton

  -- product construction: intersection

  intersection : Automaton {ℓ} Σ → Automaton {ℓ} Σ → Automaton Σ
  intersection A₁ A₂ = record {
    Q = Q₁ × Q₂ ;
    δ = λ{ (q₁ , q₂) a → δ₁ q₁ a , δ₂ q₂ a} ;
    qinit = qinit₁ , qinit₂ ;
    F = λ{ (FA , FB) → F₁ FA × F₂ FB}
    }
    where
      open Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁ ; F to F₁)
      open Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂ ; F to F₂)

  module Intersection (A B : Automaton{ℓ} Σ) where
    open Automaton A renaming (Q to QA; δ to δA) hiding (accepts)
    open Automaton B renaming (Q to QB; δ to δB) hiding (accepts)

    intersection-left : (qa : QA) (qb : QB)
      → accepts (intersection A B) (qa , qb) ⊆ (accepts A qa ∩ accepts B qb)
    intersection-left qa qb ε ε∈ = ε∈
    intersection-left qa qb (a ∷ w) aw∈ = intersection-left (δA qa a) (δB qb a) w aw∈

    intersection-right : (qa : QA) (qb : QB)
      → (accepts A qa ∩ accepts B qb) ⊆ accepts (intersection A B) (qa , qb)
    intersection-right qa qb ε ε∈ = ε∈
    intersection-right qa qb (a ∷ w) aw∈ = intersection-right (δA qa a) (δB qb a) w aw∈

    aux : (qa : QA) (qb : QB)
      → accepts (intersection A B) (qa , qb) ≐ (accepts A qa ∩ accepts B qb)
    aux qa qb = intersection-left qa qb , intersection-right qa qb

  intersection-correct : (A B : Automaton{ℓ} Σ) → Lang (intersection A B) ≐ (Lang A ∩ Lang B)
  intersection-correct A B = Intersection.aux A B (qinit A) (qinit B)

  -- product construction: union

  union : Automaton{ℓ} Σ → Automaton{ℓ} Σ → Automaton Σ
  union A B = record {
    Q = (Q A) × (Q B) ;
    δ = λ{ (qa , qb) a → δ A qa a , δ B qb a} ;
    qinit = qinit A , qinit B ;
    F = λ{ (FA , FB) → F A FA ⊎ F B FB}
    }


  module Union (A B : Automaton{ℓ} Σ) where
    open Automaton A renaming (Q to QA; δ to δA) hiding (accepts)
    open Automaton B renaming (Q to QB; δ to δB) hiding (accepts)

    union-left : (qa : QA) (qb : QB)
      → accepts (union A B) (qa , qb) ⊆ (accepts A qa ∪ accepts B qb)
    union-left qa qb ε ε∈ = ε∈
    union-left qa qb (a ∷ w) aw∈ = union-left (δA qa a) (δB qb a) w aw∈

    union-right : (qa : QA) (qb : QB)
      → (accepts A qa ∪ accepts B qb) ⊆ accepts (union A B) (qa , qb)
    union-right qa qb ε ε∈ = ε∈
    union-right qa qb (a ∷ w) aw∈ = union-right (δA qa a) (δB qb a) w aw∈

  union-correct : (A B : Automaton{ℓ} Σ) → Lang (union A B) ≐ (Lang A ∪ Lang B)
  union-correct A B  = Union.union-left A B (qinit A) (qinit B) , Union.union-right A B (qinit A) (qinit B)

  -- complement

  complement : Automaton{ℓ} Σ → Automaton Σ
  complement A = record { Q = Q A ; δ = δ A ; qinit = qinit A ; F = λ x → ¬ F A x }

  module Complement (A : Automaton{ℓ} Σ) where
    open Automaton A renaming (Q to QA; δ to δA) hiding (accepts)

    complement-left : (qa : QA)
      → accepts (complement A) qa ⊆ ∁ (accepts A qa)
    complement-left qa ε ε∉ ε∈ = contradiction ε∈ ε∉
    complement-left qa (a ∷ w) aw∉ aw∈ = complement-left (δA qa a) w aw∉ aw∈

    complement-right : (qa : QA)
      → ∁ (accepts A qa) ⊆ accepts (complement A) qa
    complement-right qa ε ε∉ = ε∉
    complement-right qa (a ∷ w) aw∉ = complement-right (δA qa a) w aw∉

  complement-correct :
    (A : Automaton{ℓ} Σ)
    → Lang (complement A) ≐ ∁ (Lang A)
  complement-correct A = Complement.complement-left A (qinit A) , Complement.complement-right A (qinit A)
