module Arden where

open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_; length) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; ≤-refl; ≤-reflexive; +-monoˡ-≤)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_; _∪_) renaming (_≐′_ to _≐_; _⊆′_ to _⊆_)

open import Language

module _ {Σ : Set} where

  -- Arden's lemma
  -- solving regular equations of the form X = AX+B
  -- both directions by strong induction simulated by mathematical induction on the length of the word

  ardens-left-gen : ∀ {A B X : Language Σ} → X ≐ (A · X) ∪ B → ε ∉ A
    → ∀ n (w : Word Σ) → length w < n → w ∈ X → w ∈ (A ∗) · B
  ardens-left-gen X=AX+B ε∉A (suc n) ε (s≤s z≤n) w∈X
    with X=AX+B .proj₁ ε w∈X
  ... | inj₂ w∈B = ε , ε , refl , (zero , tt) , w∈B
  ... | inj₁ (ε , v , refl , u∈A , v∈X)
    = contradiction u∈A ε∉A
  ardens-left-gen X=AX+B ε∉A (suc n) (a ∷ w) (s≤s lenw≤n) w∈X
    with X=AX+B .proj₁ (a ∷ w) w∈X
  ... | inj₂ w∈B = ε , a ∷ w , refl , (zero , tt) , w∈B
  ... | inj₁ (ε , v , aw=u++v , u∈A , v∈X) = contradiction u∈A ε∉A
  ... | inj₁ (a ∷ u , v , refl , u∈A , v∈X)
    with ardens-left-gen X=AX+B ε∉A n v (≤-<-trans (≤-trans (+-monoˡ-≤ (length v) z≤n) (≤-reflexive (sym (length-++ u)))) lenw≤n) v∈X
  ... | ua* , vb , refl , (j , ua*∈A↑j) , vb∈B
    = (a ∷ u ++ ua*) , vb , (cong (_ ∷_) (sym (++-assoc u ua* vb))) , (suc j , _ ∷ u , ua* , refl , u∈A , ua*∈A↑j) , vb∈B
  
  ardens-left :  ∀ {A B X : Language Σ} → X ≐ (A · X) ∪ B → ε ∉ A → X ⊆ (A ∗) · B
  ardens-left X=AX+B ε∉A w w∈X
    = ardens-left-gen X=AX+B ε∉A (suc (length w)) w ≤-refl w∈X

  ardens-right-gen : ∀ {A B X : Language Σ} → X ≐ (A · X) ∪ B → ε ∉ A
    → ∀ n (w : Word Σ) → length w < n → w ∈ (A ∗) · B → w ∈ X
  ardens-right-gen {A}{B}{X} X=AX+B ε∉A = aux
    where
      aux : ∀ n (w : Word Σ) → length w < n → w ∈ (A ∗) · B → w ∈ X
      aux (suc n) ε lenw<n (ε , v , refl , (zero , u∈A*) , v∈B) = X=AX+B .proj₂ ε (inj₂ v∈B)
      aux (suc n) ε lenw<n (ε , v , refl , (suc j , u∈A*) , v∈B)
        using (ε∈A , _) ← ε∈-concat u∈A*
        = contradiction ε∈A ε∉A
      aux (suc n) (a ∷ w) (s≤s lenw<n) (ε , v , refl , u∈A* , v∈B) = X=AX+B .proj₂ (a ∷ w) (inj₂ v∈B)
      aux (suc n) (a ∷ w) (s≤s lenw<n) (a ∷ u , v , refl , (suc j , ε , uaj , eq-uaj , ua∈A , uaj∈A↑j) , v∈B) = contradiction ua∈A ε∉A
      aux (suc n) (a ∷ w) (s≤s lenw<n) (a ∷ u , v , refl , (suc j , a ∷ ua , uaj , refl , ua∈A , uaj∈A↑j) , v∈B)
        with aux n (uaj ++ v) (≤-<-trans (≤-trans (≤-trans (+-monoˡ-≤ (length (uaj ++ v)) z≤n) (≤-reflexive (sym (length-++ ua)))) (≤-reflexive (cong length (sym (++-assoc ua uaj v))))) lenw<n) (uaj , v , refl , (j , uaj∈A↑j) , v∈B)
      ... | ih = X=AX+B .proj₂ (a ∷ w) (inj₁ (a ∷ ua , uaj ++ v , cong (_ ∷_) (++-assoc ua uaj v) , (ua∈A , ih)))
  
  ardens-right : ∀ {A B X : Language Σ} → X ≐ (A · X) ∪ B → ε ∉ A → (A ∗) · B ⊆ X
  ardens-right X=AX+B ε∉A w w∈A*B
    = ardens-right-gen  X=AX+B ε∉A (suc (length w)) w ≤-refl w∈A*B

  ardens-lemma : ∀ {A B X : Language Σ} → X ≐ (A · X) ∪ B → ε ∉ A → X ≐ (A ∗) · B
  ardens-lemma X=AX+B ε∉
    = ardens-left X=AX+B ε∉
    , ardens-right X=AX+B ε∉
