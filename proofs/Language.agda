module Language where

open import Level using (Level; _⊔_) renaming (suc to lsuc)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_)

variable ℓ ℓ₁ ℓ₂ : Level

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)


data Σabc : Set where a b c : Σabc

_ : Word Σabc
_ = ε

_ : Word Σabc
_ = a ∷ b ∷ ε

Language : Set → Set₁
Language Σ = Word Σ → Set

module _ {Σ : Set} where

  -- set operations

  Σ⋆ : Language Σ
  Σ⋆ w = ⊤

  ∅ : Language Σ
  ∅ w = ⊥

  _∩_ : Language Σ → Language Σ → Language Σ
  (L₁ ∩ L₂) w = L₁ w × L₂ w

  _∪_ : Language Σ → Language Σ → Language Σ
  (L₁ ∪ L₂) w = L₁ w ⊎ L₂ w

  ∁ : Language Σ → Language Σ
  ∁ L w = w ∉ L

  _⊆_ : Language Σ → Language Σ → Set
  L₁ ⊆ L₂ = ∀ w → L₁ w → L₂ w

  _≐_ : Language Σ → Language Σ → Set
  L₁ ≐ L₂ = L₁ ⊆ L₂ × L₂ ⊆ L₁

  lemma-∩ : (L : Language Σ) → (L ∩ Σ⋆) ≐ L
  lemma-∩ L = (λ{ w (w∈L , w∈Σ⋆) → w∈L}) , λ{ w w∈L → w∈L , tt}

  𝟙 : Language Σ
  𝟙 ε = ⊤
  𝟙 (x ∷ w) = ⊥

  _·_ : Language Σ → Language Σ → Language Σ
  (L₁ · L₂) w = ∃[ u ] ∃[ v ] (w ≡ u ++ v × L₁ u × L₂ v)

  -- monoid

  ε-cancel-right : ∀ {u v : Word Σ} → u ≡ v ++ ε → u ≡ v
  ε-cancel-right {u}{v} eq = trans eq (++-identityʳ v)

  identityˡ : (L : Language Σ) → (𝟙 · L) ≐ L
  identityˡ L = (λ{ w (ε , _ , refl , tt , w∈L) → w∈L}) , λ{ w w∈L → ε , w , refl , tt , w∈L}

  identityʳ : (L : Language Σ) → (L · 𝟙) ≐ L
  identityʳ L = (λ w → λ{ (w' , ε , w≡wε , w'∈L , x) → subst L (sym (ε-cancel-right w≡wε)) w'∈L})
              , λ w w∈ → w , ε , sym (++-identityʳ w) , w∈ , tt

  ·-assoc : (L₁ L₂ L₃ : Language Σ) → ((L₁ · L₂) · L₃) ≐ (L₁ · (L₂ · L₃))
  ·-assoc L₁ L₂ L₃ = assoc-left , assoc-right
          where
            assoc-left : ((L₁ · L₂) · L₃) ⊆ (L₁ · (L₂ · L₃))
            assoc-left w (u₁₂ , u₃ , refl , (u₁ , u₂ , refl , u₁∈ , u₂∈) , u₃∈)
              rewrite ++-assoc u₁ u₂ u₃ = u₁ , ((u₂ ++ u₃) , (refl , (u₁∈ , u₂ , u₃ , refl , u₂∈ , u₃∈)))
            assoc-right : (L₁ · (L₂ · L₃)) ⊆ ((L₁ · L₂) · L₃)
            assoc-right w (u₁ , u₂₃ , refl , u₁∈ , u₂ , u₃ , refl , u₂∈ , u₃∈)
              rewrite sym (++-assoc u₁ u₂ u₃) = u₁ ++ u₂ , u₃ , refl , (u₁ , u₂ , refl , u₁∈ , u₂∈) , u₃∈

  -- power

  _↑_ : Language Σ → ℕ → Language Σ
  L ↑ zero = 𝟙
  L ↑ suc n = L · (L ↑ n)

  -- Kleene star

  _∗ : Language Σ → Language Σ
  (L ∗) w = ∃[ n ] (L ↑ n) w

  _⁺ : Language Σ → Language Σ
  (L ⁺) w = ∃[ n ] (L ↑ suc n) w

  lemma-∗-+ : (L : Language Σ) → (L ∗) ≐ ((L ⁺) ∪ 𝟙)
  lemma-∗-+ L = (λ{ w (zero , w∈𝟙) → inj₂ w∈𝟙 ; w (suc n , w∈LLn) → inj₁ (n , w∈LLn)})
              , λ{ w (inj₁ (n , w∈LLn)) → (suc n) , w∈LLn ; w (inj₂ w∈𝟙) → zero , w∈𝟙}

  -- zero

  ∅-cancelˡ : (L : Language Σ) → (∅ · L) ≐ ∅
  ∅-cancelˡ L = (λ{ w ()}) , λ{ w ()}

  ∅-cancelʳ : (L : Language Σ) → (L · ∅) ≐ ∅
  ∅-cancelʳ L = (λ w ()) , (λ w ())
  
  
