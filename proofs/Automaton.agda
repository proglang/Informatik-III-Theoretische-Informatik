module Automaton where

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
open import Relation.Unary using (_∈_; _∉_)

open import Language
open import Isomorphism using (Iso; _↔_)


-- automaton

record Automaton (Σ : Set) : Set (lsuc ℓ) where
  field
    Q : Set ℓ
    δ : Q → Σ → Q
    qinit : Q
    F : Q → Set

  δ̃ : Q → Word Σ → Q
  δ̃ q ε = q
  δ̃ q (x ∷ w) = δ̃ (δ q x) w

  accepts : Q → Language Σ
  accepts q w = δ̃ q w ∈ F

  Lang : Language Σ
  Lang = accepts qinit

  reachable : Q → Set _
  reachable q = ∃[ w ] δ̃ qinit w ≡ q
  
  _≈_ : Q → Q → Set
  p ≈ q = ∀ w → (δ̃ p w ∈ F) ↔ (δ̃ q w ∈ F)

module _ {Σ} (A : Automaton{ℓ} Σ) where
  open Automaton A

  -- ≈ is equivalence
  ≈-refl : ∀ {q} → q ≈ q
  ≈-refl w = (λ z → z) , (λ z → z)

  ≈-refl-eq : ∀ {p q} → p ≡ q → p ≈ q
  ≈-refl-eq refl = ≈-refl

  ≈-sym : ∀ {q p} → p ≈ q → q ≈ p
  ≈-sym p≈q w = swap (p≈q w)

  ≈-trans : ∀ {p q r} → p ≈ q → q ≈ r → p ≈ r
  ≈-trans p≈q q≈r w with p≈q w | q≈r w
  ... | pq₁ , pq₂ | qr₁ , qr₂ = (λ z → qr₁ (pq₁ z)) , (λ z → pq₂ (qr₂ z))

  -- ≈ is compatible
  ≈-compatible : ∀ {p q} {x} → p ≈ q → δ p x ≈ δ q x
  ≈-compatible {x = x} p≈q w = p≈q (x ∷ w)

  ≈-final : ∀ p q → F p → p ≈ q → F q
  ≈-final p q p∈ p≈q = p≈q ε .proj₁ p∈

  -- equivalence classes
  
  ≈-class : (X : Q → Set) → Set _
  ≈-class X = ∃[ p ] p ∈ X × ∀ q → (q ∈ X) ↔ (p ≈ q)
  
  -- equivalence class of a state p

  [_]≈ : Q → Q → Set
  [ p ]≈ = λ q → p ≈ q

  is-≈-class : ∀ p → ≈-class ([ p ]≈)
  is-≈-class p₀ = p₀ , ≈-refl , (λ q → (λ z → z) , λ z → z)


  ≈-automaton : Automaton Σ
  ≈-automaton = record {
    Q = ΣΣ (Q → Set) ≈-class ;
    δ = λ{ ([q] , q , [q]-class) x → [ δ q x ]≈ , is-≈-class _} ;
    qinit = [ qinit ]≈ , is-≈-class _ ;
    F = λ{ ([q] , q , [q]-class) → q ∈ F} }

  -- set of representatives of equivalence classes
  record Part (R : Q → Set) p : Set (lsuc ℓ) where
    field
      rep  : Q
      rep∈ : rep ∈ R
      rep≈ : p ≈ rep

  record Reps : Set (lsuc ℓ)  where
    field
      Q′    : Set
      R     : Q → Set
      disj  : ([p] [q] : ΣΣ Q R) → [p] .proj₁ ≈ [q] .proj₁ → [p] .proj₁ ≡ [q] .proj₁
      part  : ∀ p → ∃[ q ] q ∈ R × p ≈ q
      iso   : Iso Q′ (ΣΣ Q R)

  postulate
    reps-of : Reps

  rep-automaton : Automaton Σ
  rep-automaton =
    let open Reps reps-of
        open Iso iso
    in
    record {
      Q = Q′ ;
      δ = λ q′ x → let qin , rin = fwd q′
                       qout = δ qin x
                       qoutrep , qoutrep∈R , qrep≈ = part qout
                   in  bwd (qoutrep , qoutrep∈R) ;
      qinit = let qinitrep , qinit∈R , qrep≈ = part qinit
              in  bwd (qinitrep , qinit∈R) ;
      F = λ q′ → let qf , rf = fwd q′
                 in  F qf
      }

      
