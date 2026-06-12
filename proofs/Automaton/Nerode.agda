module Automaton.Nerode where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst; subst₂)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (_∈_; _∉_) renaming (_≐′_ to  _≐_; _⊆′_ to  _⊆_)

open import Language
open import Isomorphism using (Iso; _↔_)
open import Sets using (｛｝)
open import Automaton.Congruence using (module Equiv) 
open import Automaton as DET

module _ {Σ}{L : Language Σ} where

  -- the Nerode relation for L

  _≋_ : Word Σ → Word Σ → Set
  _≋_ u v = ∀ w → ((u ++ w) ∈ L) ↔ ((v ++ w) ∈ L)

  -- ... is an equivalence relation

  ≋-refl : ∀ {u} → u ≋ u
  ≋-refl = λ w → (λ z → z) , (λ z → z)

  ≋-sym : ∀ {u}{v} → u ≋ v → v ≋ u
  ≋-sym u≋v = λ w → u≋v w .proj₂ , u≋v w .proj₁

  ≋-trans : ∀ {u}{v}{w} → u ≋ v → v ≋ w → u ≋ w
  ≋-trans u≋v v≋w = λ w₁ →
                       (λ z → v≋w w₁ .proj₁ (u≋v w₁ .proj₁ z)) ,
                       (λ z → u≋v w₁ .proj₂ (v≋w w₁ .proj₂ z))

  -- ... and a right congruence

  ≋-right-congruence : ∀ {u}{v} → u ≋ v → ∀ w → (u ++ w) ≋ (v ++ w)
  ≋-right-congruence {u}{v} u≋v w z
    rewrite ++-assoc u w z | ++-assoc v w z
    = u≋v (w ++ z)

  open Equiv _≋_ ≋-refl

  ≋-automaton : Automaton Σ
  ≋-automaton = record
    { Q      = ΣΣ (Word Σ → Set) Class -- states are equivalence classes of words
    ; δ      = δ-map
    ; qinit  = [ ε ]≈ , is-Class
    ; F      = λ{ ([w] , _) → [w] ⊆ L }
    }
    where
      δ-map : _
      δ-map ([w] , Equiv.⟨ w , w∈[w] , closed ⟩) a
        = ｛ v ∣ ∃[ w ] w ∈ [w] × v ≋ (w ++ [ a ]) ｝
        , Equiv.⟨ w ++ [ a ]
                , (w , w∈[w] , ≋-refl)
                , (λ v′ → (λ{ (w′ , w′∈[w] , w≋) z → ≋-trans (≋-right-congruence (closed w′ .proj₁  w′∈[w]) [ a ]) (≋-sym w≋) z .proj₁
                                                   , ≋-trans w≋ (≋-sym (≋-right-congruence (closed w′ .proj₁  w′∈[w]) [ a ])) z .proj₁ })
                        , λ wa≋v′ → w , w∈[w] , ≋-sym wa≋v′ ) ⟩

  -- rep-automaton : Automaton Σ
  -- rep-automaton =
  --   let open Reps reps-of
  --       open Iso iso
  --   in
  --   record
  --     { Q      = Q′
  --     ; δ      = λ [q] a → let qin = fwd [q] .proj₁
  --                              qoutrep , qoutrep∈R , qrep≈ = part (δ qin a)
  --                          in  bwd (qoutrep , qoutrep∈R)
  --     ; qinit  = let qinitrep , qinit∈R , qrep≈ = part qinit
  --                in  bwd (qinitrep , qinit∈R)
  --     ; F      = λ q′ → let qf , rf = fwd q′ in F qf
  --     }
  
