module SubsetFixedPoint where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; T; _≟_)
open import Data.Nat using (ℕ; zero; suc; _^_; _≤_; z≤n; s≤s;_<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m<n⇒m<1+n; ≤-<-trans ;_≤?_ ; _≥?_ ; _<?_ ; _>?_; ≮⇒≥; ≤-antisym; 1+n≰n)
open import Data.Fin using (Fin; zero; suc; finToFun; funToFin)
open import Data.Fin.Subset using (Subset; Side; inside; outside; ∣_∣) renaming (_∈_ to _∈′_; _∉_ to _∉′_; _⊆_ to _⊆′_; _⊂_ to _⊂′_; ⊥ to ∅′)
open import Data.Fin.Subset.Properties using (∣⊥∣≡0; p⊆q⇒∣p∣≤∣q∣; p⊂q⇒∣p∣<∣q∣; ⊥⊆; drop-∷-⊆;∣p∣≤n)
open import Data.Fin.Properties using (funToFin-finToFin; finToFun-funToFin)
open import Data.Vec using (Vec; []; _∷_; tabulate; lookup; replicate; _[_]=_; here; there; count)
open import Data.Vec.Properties using (tabulate∘lookup; lookup∘tabulate; ≡-dec)
open import Data.Product using (∃; ∃-syntax; _×_; _,_) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)

-- utility

⊆-≢⇒⊂ : ∀ {n} {M₁ M₂ : Subset n} → M₁ ⊆′ M₂ → M₁ ≢ M₂ → M₁ ⊂′ M₂
⊆-≢⇒⊂ M₁⊆M₂ M₁≢M₂ = M₁⊆M₂ , aux M₁⊆M₂ M₁≢M₂
  where
    aux : ∀ {n} {M₁ M₂ : Subset n} → M₁ ⊆′ M₂ → M₁ ≢ M₂ → ∃ (λ x → x ∈′ M₂ × x ∉′ M₁)
    aux {zero} {[]} {[]} M₁⊆M₂ M₁≢M₂ = ⊥-elim (M₁≢M₂ refl)
    aux {suc n} {outside ∷ M₁} {outside ∷ M₂} M₁⊆M₂ M₁≢M₂
      with aux {n} {M₁} {M₂} (drop-∷-⊆ M₁⊆M₂) (λ{ refl → M₁≢M₂ refl})
    ... | k , M₂[k]=true , ¬M₁[k]=true = suc k , (there M₂[k]=true) , (λ{ (there x) → ¬M₁[k]=true x})
    aux {suc n} {outside ∷ M₁} {true ∷ M₂} M₁⊆M₂ M₁≢M₂ = zero , here , (λ ())
    aux {suc n} {true ∷ M₁} {outside ∷ M₂} M₁⊆M₂ M₁≢M₂
      with M₁⊆M₂ {zero} here
    ... | ()
    aux {suc n} {true ∷ M₁} {true ∷ M₂} M₁⊆M₂ M₁≢M₂
      with aux {n} {M₁} {M₂} (drop-∷-⊆ M₁⊆M₂) (λ{ refl → M₁≢M₂ refl})
    ... | k , M₂[k]=true , ¬M₁[k]=true = suc k , (there M₂[k]=true) , (λ{ (there x) → ¬M₁[k]=true x})

-- subsets

module _ {n : ℕ} (step : Subset n → Subset n) where

  Monotonic : Set
  Monotonic = ∀ {M₁}{M₂} → M₁ ⊆′ M₂ → step M₁ ⊆′ step M₂

  Fixed-Point : Subset n → Set
  Fixed-Point M = M ≡ step M

  iterate :  ∀ (i : ℕ) → Subset n
  iterate zero = ∅′
  iterate (suc i) = step (iterate i)

  StableAt : ℕ → Set
  StableAt i = Fixed-Point (iterate i)

  StrictAt :  ℕ → Set
  StrictAt i = iterate i ⊂′ iterate (suc i)

  ⊆-increasing : Monotonic → ∀ i → iterate i ⊆′ iterate (suc i)
  ⊆-increasing mono zero = ⊥⊆
  ⊆-increasing mono (suc i) = mono (⊆-increasing mono i)

  strict-chain-cardinality :
    ∀ k →
    (∀ i → i < k → StrictAt i) →
    k ≤ ∣ iterate k ∣
  strict-chain-cardinality zero inv = z≤n
  strict-chain-cardinality (suc k) inv
    with strict-chain-cardinality k (λ i i<k → inv i (m<n⇒m<1+n i<k))
  ... | ih
    = ≤-<-trans ih (p⊂q⇒∣p∣<∣q∣ (inv k ≤-refl))

  bounded-search : Monotonic
    → ∀ k → StableAt k ⊎ ∀ i → i < k → StrictAt i
  bounded-search mono zero = inj₂ (λ i ())
  bounded-search mono (suc k)
    with bounded-search mono k
  ... | inj₁ k≡step-k rewrite sym k≡step-k = inj₁ k≡step-k
  ... | inj₂ ih
    using M ← iterate k
    with ≡-dec _≟_ M (step M)
  ... | yes M≡step-M = inj₁ (cong step M≡step-M)
  ... | no ¬M≡step-M = inj₂ (λ{ i (s≤s i≤k)
                        → case i <? k of λ where
                          (yes i<k) → ih i i<k
                          (no ¬i<k) → case ≤-antisym i≤k (≮⇒≥ ¬i<k) of
                                      λ{ refl → ⊆-≢⇒⊂ (λ {j} → ⊆-increasing mono k) ¬M≡step-M}})

  fixed-point-iteration : Monotonic
    → ∃[ k ] Fixed-Point (iterate k)
  fixed-point-iteration mono
    with bounded-search mono (suc n)
  ... | inj₁ stableAtN = suc n , stableAtN
  ... | inj₂ strictUntilN
    using r ← strict-chain-cardinality (suc n) strictUntilN
    = ⊥-elim (1+n≰n (≤-trans r (∣p∣≤n (step (iterate n)))))
