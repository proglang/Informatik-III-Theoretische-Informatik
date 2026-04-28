module Automaton where

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

open import Language


record Iso (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field fwd : A → B
        bwd : B → A
        fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
        bwd∘fwd : ∀ a → bwd (fwd a) ≡ a


-- automaton

record Automaton (Σ : Set) : Set (lsuc ℓ) where
  field
    Q : Set ℓ
    δ : Q → Σ → Q
    qinit : Q
    F : Q → Set

module _ {Σ} (A : Automaton{ℓ} Σ) where
  open Automaton A

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

  record Reps : Set (lsuc ℓ)  where
    field
      Q′ : Set
      R : Q → Set
      disj : ∀ p q → p ∈ R × q ∈ R → p ≈ q → p ≡ q
      part : ∀ p → ∃[ q ] q ∈ R × p ≈ q
      iso : Iso Q′ (ΣΣ Q R)

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
                   in bwd (qoutrep , qoutrep∈R) ;
      qinit = let qinitrep , qinit∈R , qrep≈ = part qinit
              in bwd (qinitrep , qinit∈R) ;
      F = λ q′ → let qf , rf = fwd q′
                 in F qf
      }

      
module _ {Σ} where
  open Automaton

  accepts-left   : (A : Automaton{ℓ} Σ) → (q : Q A) →
    let open Reps (reps-of A)
        qrep , qrep∈R , qrep≈ = part q
    in  accepts (rep-automaton A) (Iso.bwd iso (qrep , qrep∈R)) ⊆ accepts A q
  accepts-left A q ε ε∈ = let open Reps (reps-of A)
                              qrep , qrep∈R , qrep≈ = part q
                              q′ = subst (F A) (cong proj₁ (Iso.fwd∘bwd iso (qrep , qrep∈R))) ε∈
                          in  ≈-final A qrep q q′ (≈-sym A qrep≈)
  accepts-left A q (x ∷ w) xw∈ = {!!}


  accepts-right  : (A : Automaton{ℓ} Σ) → (q : Q A) →
    let open Reps (reps-of A)
        qrep , qrep∈R , qrep≈ = part q
    in  accepts A q ⊆ accepts (rep-automaton A) (Iso.bwd iso (qrep , qrep∈R))
  accepts-right A q ε ε∈ = let open Reps (reps-of A)
                               open Iso iso
                               qrep , qrep∈R , qrep≈ = part q
                               q≈ : _≈_ A qrep (fwd (bwd (qrep , qrep∈R)) .proj₁)
                               q≈ = ≈-refl-eq A (cong proj₁ (sym (fwd∘bwd (qrep , qrep∈R))))
                           in ≈-final A q
                                   (fwd (bwd (qrep , qrep∈R)) .proj₁) ε∈ (≈-trans A qrep≈ q≈)
  accepts-right A q (x ∷ w) xw∈ = {!!}

  rep-automaton-correct : (A : Automaton{ℓ} Σ) → Lang (rep-automaton A) ≐ Lang A 
  rep-automaton-correct A = accepts-left A (qinit A) , accepts-right A (qinit A)
      


module _ {Σ} where
  open Automaton

  -- product construction: intersection

  intersection : Automaton {ℓ} Σ → Automaton {ℓ} Σ → Automaton Σ
  intersection A B = record {
    Q = Q A × Q B ;
    δ = λ{ (qa , qb) x → δ A qa x , δ B qb x} ;
    qinit = qinit A , qinit B ;
    F = λ{ (FA , FB) → F A FA × F B FB}
    }

  intersection-left :
    (A B : Automaton{ℓ} Σ) (qa : Q A) (qb : Q B)
    → accepts (intersection A B) (qa , qb) ⊆ (accepts A qa ∩ accepts B qb)
  intersection-left A B qa qb ε ε∈ = ε∈
  intersection-left A B qa qb (x ∷ w) xw∈ = intersection-left A B (δ A qa x) (δ B qb x) w xw∈

  intersection-right :
    (A B : Automaton{ℓ} Σ) (qa : Q A) (qb : Q B)
    → (accepts A qa ∩ accepts B qb) ⊆ accepts (intersection A B) (qa , qb)
  intersection-right A B qa qb ε ε∈ = ε∈
  intersection-right A B qa qb (x ∷ w) xw∈ = intersection-right A B (δ A qa x) (δ B qb x) w xw∈

  intersection-aux :
    (A B : Automaton{ℓ} Σ) (qa : Q A) (qb : Q B)
    → accepts (intersection A B) (qa , qb) ≐ (accepts A qa ∩ accepts B qb)
  intersection-aux A B qa qb = (intersection-left A B qa qb) , (intersection-right A B qa qb)

  intersection-correct : (A B : Automaton{ℓ} Σ) → Lang (intersection A B) ≐ (Lang A ∩ Lang B)
  intersection-correct A B = intersection-aux A B (qinit A) (qinit B)

  -- product construction: union

  union : Automaton{ℓ} Σ → Automaton{ℓ} Σ → Automaton Σ
  union A B = record {
    Q = (Q A) × (Q B) ;
    δ = λ{ (qa , qb) x → δ A qa x , δ B qb x} ;
    qinit = qinit A , qinit B ;
    F = λ{ (FA , FB) → F A FA ⊎ F B FB}
    }

  union-left :
    (A B : Automaton{ℓ} Σ) (qa : Q A) (qb : Q B)
    → accepts (union A B) (qa , qb) ⊆ (accepts A qa ∪ accepts B qb)
  union-left A B qa qb ε ε∈ = ε∈
  union-left A B qa qb (x ∷ w) xw∈ = union-left A B (δ A qa x) (δ B qb x) w xw∈

  union-right :
    (A B : Automaton{ℓ} Σ) (qa : Q A) (qb : Q B)
    → (accepts A qa ∪ accepts B qb) ⊆ accepts (union A B) (qa , qb)
  union-right A B qa qb ε ε∈ = ε∈
  union-right A B qa qb (x ∷ w) xw∈ = union-right A B (δ A qa x) (δ B qb x) w xw∈

  union-correct : (A B : Automaton{ℓ} Σ) → Lang (union A B) ≐ (Lang A ∪ Lang B)
  union-correct A B  = union-left A B (qinit A) (qinit B) , union-right A B (qinit A) (qinit B)

  -- complement

  complement : Automaton{ℓ} Σ → Automaton Σ
  complement A = record { Q = Q A ; δ = δ A ; qinit = qinit A ; F = λ x → ¬ F A x }

  complement-left :
    (A : Automaton{ℓ} Σ) (qa : Q A)
    → accepts (complement A) qa ⊆ ∁ (accepts A qa)
  complement-left A qa ε ε∉ ε∈ = contradiction ε∈ ε∉
  complement-left A qa (x ∷ w) xw∉ xw∈ = complement-left A (δ A qa x) w xw∉ xw∈

  complement-right :
    (A : Automaton{ℓ} Σ) (qa : Q A)
    → ∁ (accepts A qa) ⊆ accepts (complement A) qa
  complement-right A qa ε ε∉ = ε∉
  complement-right A qa (x ∷ w) xw∉ = complement-right A (δ A qa x) w xw∉

  complement-correct :
    (A : Automaton{ℓ} Σ)
    → Lang (complement A) ≐ ∁ (Lang A)
  complement-correct A = complement-left A (qinit A) , complement-right A (qinit A)
