module Automaton.Congruence where

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
open import Relation.Unary using (_∈_; _∉_) renaming (_≐′_ to  _≐_; _⊆′_ to  _⊆_)
open import Function using (id)

open import Language
open import Isomorphism using (Iso; _↔_)

open import Automaton as DET

module Equiv {ℓ}{A : Set ℓ}(_≈_ : A → A → Set) (≈-refl : ∀ {q} → q ≈ q) where

  record Part (R : A → Set) p : Set (lsuc ℓ) where
    field
      rep   : A
      rep∈  : rep ∈ R
      rep≈  : p ≈ rep

  -- set of representatives of equivalence classes

  record Class (X : A → Set) : Set ℓ where
    constructor ⟨_,_,_⟩
    field
      elem   : A
      elem∈  : elem ∈ X
      closed : ∀ x → (x ∈ X) ↔ (elem ≈ x)

  ≈-class : (X : A → Set) → Set _
  ≈-class X = ∃[ p ] p ∈ X × ∀ q → (q ∈ X) ↔ (p ≈ q)

  -- equivalence class of a state p

  [_]≈ : A → A → Set
  [ p ]≈ = λ q → p ≈ q

  is-≈-class : ∀ p → ≈-class ([ p ]≈)
  is-≈-class p₀ = p₀ , ≈-refl , (λ q → (λ z → z) , λ z → z)

  is-Class : ∀ {p} → Class ([ p ]≈)
  is-Class {p} = record
    { elem = p
    ; elem∈ = ≈-refl
    ; closed = λ x → id , id
    }

  record Reps : Set (lsuc ℓ)  where
    field
      Q′    : Set
      R     : A → Set
      disj  : ([p] [q] : ΣΣ A R) → [p] .proj₁ ≈ [q] .proj₁ → [p] .proj₁ ≡ [q] .proj₁
      part  : ∀ p → ∃[ q ] q ∈ R × p ≈ q
      -- part′ : ∀ p → Part R p -- equivalent alternative
      iso   : Iso Q′ (ΣΣ A R)

  postulate
    reps-of : Reps


module A-congruence {Σ} {A : Automaton{ℓ} Σ} where
  open Automaton A

  _≈_ : Q → Q → Set
  p ≈ q = ∀ w → (δ̃ p w ∈ F) ↔ (δ̃ q w ∈ F)

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

  open Equiv _≈_ ≈-refl
  

  ≈-automaton : Automaton Σ
  ≈-automaton = record {
    Q = ΣΣ (Q → Set) ≈-class ;
    δ = λ{ ([q] , q , [q]-class) x → [ δ q x ]≈ , is-≈-class _} ;
    qinit = [ qinit ]≈ , is-≈-class _ ;
    F = λ{ ([q] , q , [q]-class) → q ∈ F} }

  rep-automaton : Automaton Σ
  rep-automaton =
    let open Reps reps-of
        open Iso iso
    in
    record
      { Q      = Q′
      ; δ      = λ [q] a → let qin = fwd [q] .proj₁
                               qoutrep , qoutrep∈R , qrep≈ = part (δ qin a)
                           in  bwd (qoutrep , qoutrep∈R)
      ; qinit  = let qinitrep , qinit∈R , qrep≈ = part qinit
                 in  bwd (qinitrep , qinit∈R)
      ; F      = λ q′ → let qf , rf = fwd q′ in F qf
      }

  open Automaton rep-automaton renaming (Lang to Lang≈; Q to Q≈; δ to δ≈; δ̃ to δ̃≈; F to F≈; qinit to qinit≈)
  open Reps reps-of
  open Iso iso

  delta-welldefined : ∀ a q [q] → q ≈ fwd [q] .proj₁ → δ q a ≈ fwd (δ≈ [q] a) .proj₁
  delta-welldefined a q [q] q≈[q]
    using qin ← fwd [q] .proj₁
    using part-δ-qin-a ← part (δ qin a)
    using (qoutrep , qoutrep∈R , qoutrep≈) ← part-δ-qin-a
    = δqa≈
    where
      iso-eq : _
      iso-eq = fwd∘bwd (qoutrep , qoutrep∈R)

      δqa≈′ : δ q a ≈ part (δ (fwd [q] .proj₁) a) .proj₁
      δqa≈′ = ≈-trans (λ w → q≈[q] (a ∷ w)) qoutrep≈

      δqa≈ : δ q a ≈ fwd (bwd (qoutrep , qoutrep∈R)) .proj₁
      δqa≈ rewrite iso-eq = δqa≈′

  qi-eq : _
  qi-eq = fwd∘bwd (part qinit .proj₁ , part qinit .proj₂ .proj₁)

  qi≈ : qinit ≈ fwd (bwd (part qinit .proj₁ , part qinit .proj₂ .proj₁)) .proj₁
  qi≈ rewrite qi-eq = part qinit .proj₂ .proj₂

  correct-left : Lang ⊆ Lang≈
  correct-left w w∈L = aux w qinit qinit≈ qi≈ w∈L
    where
      aux : ∀ w q [q] → q ≈ fwd [q] .proj₁ → δ̃ q w ∈ F → δ̃≈ [q] w ∈ F≈
      aux ε q [q] q≈[q] q∈F = q≈[q] ε .proj₁ q∈F
      aux (a ∷ w) q [q] q≈[q] δ̃-[δ-q-a]-w∈F
        = aux w (δ q a) (δ≈ [q] a) (delta-welldefined a q [q] q≈[q]) δ̃-[δ-q-a]-w∈F

  correct-right : Lang≈ ⊆ Lang
  correct-right w w∈L≈ = aux w qinit qinit≈ qi≈ w∈L≈
    where
      aux : ∀ w q [q] → q ≈ fwd [q] .proj₁ → δ̃≈ [q] w ∈ F≈ → δ̃ q w ∈ F
      aux ε q [q] q≈[q] [q]∈F≈ = q≈[q] ε .proj₂ [q]∈F≈
      aux (a ∷ w) q [q] q≈[q] δ̃≈-[q]-w∈F≈
        = aux w (δ q a) (δ≈ [q] a) (delta-welldefined a q [q] q≈[q]) δ̃≈-[q]-w∈F≈

  correct : Lang ≐ Lang≈
  correct .proj₁ = correct-left
  correct .proj₂ = correct-right
      
