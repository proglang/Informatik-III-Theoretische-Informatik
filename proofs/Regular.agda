module Regular where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_; ∅; _∪_; ｛_｝) renaming (_≐′_ to _≐_; _⊆′_ to _⊆_)
open import Relation.Unary.Properties using () renaming (≐′-trans to ≐-trans)

open import Language
open import ND-Automaton

-- regular expressions

data RE (Σ : Set) : Set where
  `∅ : RE Σ
  `ε : RE Σ
  `_ : Σ → RE Σ
  _`·_ : RE Σ → RE Σ → RE Σ
  _`+_ : RE Σ → RE Σ → RE Σ
  _`* : RE Σ → RE Σ

module _ {Σ : Set} where

  ⟦_⟧ : RE Σ → Language Σ
  ⟦ `∅ ⟧       = ∅
  ⟦ `ε ⟧       = 𝟙
  ⟦ ` a ⟧      = ｛ [ a ] ｝
  ⟦ r `· r₁ ⟧  = ⟦ r ⟧ · ⟦ r₁ ⟧
  ⟦ r `+ r₁ ⟧  = ⟦ r ⟧ ∪ ⟦ r₁ ⟧
  ⟦ r `* ⟧     = ⟦ r ⟧ ∗

  -- encoding of regular expressions in nondeterministic (finite) automata

  encode : RE Σ → ND-Automaton Σ
  encode `∅ = A∅
  encode `ε = Aε
  encode (` a) = Aa a
  encode (r `· r₁) = Concatenation.A· (encode r) (encode r₁)
  encode (r `+ r₁) = Union.A∪ (encode r) (encode r₁)
  encode (r `*) = Kleene2.A* (encode r)

  -- correctness of the encoding

  open ND-Automaton.ND-Automaton

  correct : ∀ r → Lang (encode r) ≐ ⟦ r ⟧
  correct `∅ = A∅-correct
  correct `ε = Aε-correct
  correct (` a) = Aa-correct a
  correct (r `· r₁)
    with correct r | correct r₁
  ... | ih← , ih→ | ih₁← , ih₁→ = ≐-trans (Concatenation.A·-correct (encode r) (encode r₁))
                              ((λ{ w (u , v , refl , Lru , Lr₁v) →
                                     u , v , refl , (ih← u Lru , ih₁← v Lr₁v)})
                              , λ{ w (u , v , refl , u∈ , v∈) →
                                   u , (v , refl , (ih→ u u∈) , ih₁→ v v∈)})
  correct (r `+ r₁)
      with correct r | correct r₁
  ... | ih← , ih→ | ih₁← , ih₁→
    = ≐-trans (Union.A∪-correct (encode r) (encode r₁))
              ((λ{ w (inj₁ w∈r) → inj₁ (ih← w w∈r)
                 ; w (inj₂ w∈r₁) → inj₂ (ih₁← w w∈r₁)})
              , λ{ w (inj₁ w∈r) → inj₁ (ih→ w w∈r)
                 ; w (inj₂ w∈r₁) → inj₂ (ih₁→ w w∈r₁)})
  correct (r `*)
    with correct r
  ... | ih← , ih→
    = ≐-trans (Kleene2.A*-correct (encode r))
              ((λ{ w (n , w∈r^n) → n , aux← n w w∈r^n})
              , λ{ w (n , w∈r^n) → n , aux→ n w w∈r^n})
    where
      aux← : ∀ n → Lang (encode r) ↑ n ⊆ ⟦ r ⟧ ↑ n
      aux← zero w w∈ = w∈
      aux← (suc n) w (u , v , refl , Lru , Lrnv)
        = u , v , refl , ih← u Lru , aux← n v Lrnv

      aux→ : ∀ n → ⟦ r ⟧ ↑ n ⊆ Lang (encode r) ↑ n
      aux→ zero w w∈ = w∈
      aux→ (suc n) w (u , v , refl , u∈r , v∈r^n)
        = u , v , refl , ih→ u u∈r , aux→ n v v∈r^n
