module DecND-Automaton where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; splitAt; join) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (splitAt-join; join-splitAt)
open import Data.Product using (∃-syntax; _×_; _,_; swap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Isomorphism using (Iso; comp; inverse-iso)
open import Finiteness using (Finite)
open import DecSets using (𝔓; Finite-𝔓)

import DecAutomaton as DET

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

FINITE : ∀ {ℓ} → Set ℓ → Set ℓ
FINITE = Finite

_↔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
A ↔ B = (A → B) × (B → A)

id-iso : ∀ {ℓ} {A : Set ℓ} → Iso A A
id-iso = record
  { fwd = λ x → x
  ; bwd = λ x → x
  ; fwd∘bwd = λ _ → refl
  ; bwd∘fwd = λ _ → refl
  }

sum-fin-iso : ∀ m n → Iso (Fin (m + n)) (Fin m ⊎ Fin n)
sum-fin-iso m n = record
  { fwd = splitAt m
  ; bwd = join m n
  ; fwd∘bwd = splitAt-join m n
  ; bwd∘fwd = join-splitAt m n
  }

iso-⊎ : ∀ {A : Set ℓ₁} {A′ : Set ℓ₂} {B : Set ℓ₃} {B′ : Set ℓ}
  → Iso A A′ → Iso B B′ → Iso (A ⊎ B) (A′ ⊎ B′)
iso-⊎ isoA isoB =
  record
    { fwd = λ { (inj₁ a) → inj₁ (Iso.fwd isoA a)
              ; (inj₂ b) → inj₂ (Iso.fwd isoB b) }
    ; bwd = λ { (inj₁ a′) → inj₁ (Iso.bwd isoA a′)
              ; (inj₂ b′) → inj₂ (Iso.bwd isoB b′) }
    ; fwd∘bwd = λ { (inj₁ a′) → cong inj₁ (Iso.fwd∘bwd isoA a′)
                  ; (inj₂ b′) → cong inj₂ (Iso.fwd∘bwd isoB b′) }
    ; bwd∘fwd = λ { (inj₁ a) → cong inj₁ (Iso.bwd∘fwd isoA a)
                  ; (inj₂ b) → cong inj₂ (Iso.bwd∘fwd isoB b) }
    }

finite-⊎ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → FINITE A → FINITE B → FINITE (A ⊎ B)
finite-⊎ (m , isoA) (n , isoB) =
  (m + n)
  , comp (iso-⊎ isoA isoB) (inverse-iso (sum-fin-iso m n))

finite-⊤ : FINITE ⊤
finite-⊤ =
  suc zero
  , record
      { fwd = λ _ → fzero
      ; bwd = λ { fzero → tt }
      ; fwd∘bwd = λ { fzero → refl }
      ; bwd∘fwd = λ { tt → refl }
      }

finite-Fin : ∀ n → FINITE (Fin n)
finite-Fin n = n , id-iso

record ND-Automaton (Σ : Set) : Set₁ where
  field
    Q      : Set
    δ      : Q → Σ → 𝔓 Q
    qinit  : Q
    F      : 𝔓 Q

  δ̃ : Q → Word Σ → Q → Set
  δ̃ q ε p = q ≡ p
  δ̃ q (a ∷ w) p = ∃[ q′ ] T (δ q a q′) × δ̃ q′ w p

  accepts : Q → Word Σ → Set
  accepts q w = ∃[ qf ] T (F qf) × δ̃ q w qf

  Lang : Word Σ → Set
  Lang = accepts qinit

  reachable : Q → Set
  reachable q = ∃[ w ] δ̃ qinit w q

  _≈_ : Q → Q → Set
  p ≈ q = ∀ w → accepts p w ↔ accepts q w

-- powerset construction

module _ {Σ : Set} where

  eqFin : ∀ {n} → Fin n → Fin n → Bool
  eqFin {zero} ()
  eqFin {suc n} fzero fzero = true
  eqFin {suc n} fzero (fsuc j) = false
  eqFin {suc n} (fsuc i) fzero = false
  eqFin {suc n} (fsuc i) (fsuc j) = eqFin i j

  anyFin : ∀ n → (Fin n → Bool) → Bool
  anyFin zero f = false
  anyFin (suc n) f = f fzero ∨ anyFin n (λ i → f (fsuc i))

  powerset : (𝓝 : ND-Automaton Σ) → FINITE (ND-Automaton.Q 𝓝) → DET.Automaton Σ
  powerset 𝓝 (n , iso) = record
    { Q = 𝔓 Qₙ
    ; δ = λ qq a p → anyQ (λ q → qq q ∧ δₙ q a p)
    ; qinit = λ q → eqQ q qinitₙ
    ; F = λ qq → anyQ (λ q → qq q ∧ Fₙ q)
    }
    where
      open ND-Automaton 𝓝
        renaming (Q to Qₙ; δ to δₙ; qinit to qinitₙ; F to Fₙ)

      anyQ : (Qₙ → Bool) → Bool
      anyQ f = anyFin n (λ i → f (Iso.bwd iso i))

      eqQ : Qₙ → Qₙ → Bool
      eqQ q p = eqFin (Iso.fwd iso q) (Iso.fwd iso p)

  finite-powerset : (𝓝 : ND-Automaton Σ) → (finQ : FINITE (ND-Automaton.Q 𝓝))
    → FINITE (DET.Automaton.Q (powerset 𝓝 finQ))
  finite-powerset 𝓝 finQ = Finite-𝔓 finQ

module _ {Σ : Set} where

  δ∅ : ⊤ → Σ → 𝔓 ⊤
  δ∅ tt a tt = false

  A∅ : ND-Automaton Σ
  A∅ = record
    { Q = ⊤
    ; δ = δ∅
    ; qinit = tt
    ; F = λ _ → false
    }

  finite-A∅ : FINITE (ND-Automaton.Q A∅)
  finite-A∅ = finite-⊤

  δε : ⊤ → Σ → 𝔓 ⊤
  δε tt a tt = false

  Aε : ND-Automaton Σ
  Aε = record
    { Q = ⊤
    ; δ = δε
    ; qinit = tt
    ; F = λ _ → true
    }

  finite-Aε : FINITE (ND-Automaton.Q Aε)
  finite-Aε = finite-⊤

  δa : (Σ → Σ → Bool) → Σ → Fin 2 → Σ → 𝔓 (Fin 2)
  δa eq a fzero      b fzero      = false
  δa eq a fzero      b (fsuc fzero) = eq a b
  δa eq a (fsuc fzero) b _          = false

  Aa : (Σ → Σ → Bool) → Σ → ND-Automaton Σ
  Aa eq a = record
    { Q = Fin 2
    ; δ = δa eq a
    ; qinit = fzero
    ; F = λ { fzero → false ; (fsuc fzero) → true }
    }

  finite-Aa : ∀ eq a → FINITE (ND-Automaton.Q (Aa eq a))
  finite-Aa eq a = finite-Fin 2

  module Concatenation (A₁ A₂ : ND-Automaton Σ) where

    open ND-Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁)
    open ND-Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; F to F₂)

    A· : ND-Automaton Σ
    A· = record
      { Q = Q₁ ⊎ Q₂
      ; δ = λ{ (inj₁ q₁) a → λ{ (inj₁ q₁′) → δ₁ q₁ a q₁′
                              ; (inj₂ q₂′) → F₁ q₁ ∧ δ₂ qinit₂ a q₂′ }
             ; (inj₂ q₂) a → λ{ (inj₁ _) → false
                              ; (inj₂ q₂′) → δ₂ q₂ a q₂′ } }
      ; qinit = inj₁ qinit₁
      ; F = λ{ (inj₁ q₁) → F₁ q₁ ∧ F₂ qinit₂
             ; (inj₂ q₂) → F₂ q₂ }
      }

    finite-A· : FINITE Q₁ → FINITE Q₂ → FINITE (ND-Automaton.Q A·)
    finite-A· = finite-⊎

  module Union (A₁ A₂ : ND-Automaton Σ) where

    open ND-Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁)
    open ND-Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; F to F₂)

    A∪ : ND-Automaton Σ
    A∪ = record
      { Q = ⊤ ⊎ (Q₁ ⊎ Q₂)
      ; δ = λ{ (inj₁ tt) a → λ{ (inj₁ _) → false
                              ; (inj₂ (inj₁ q₁′)) → δ₁ qinit₁ a q₁′
                              ; (inj₂ (inj₂ q₂′)) → δ₂ qinit₂ a q₂′ }
             ; (inj₂ (inj₁ q₁)) a → λ{ (inj₁ _) → false
                                     ; (inj₂ (inj₁ q₁′)) → δ₁ q₁ a q₁′
                                     ; (inj₂ (inj₂ _)) → false }
             ; (inj₂ (inj₂ q₂)) a → λ{ (inj₁ _) → false
                                     ; (inj₂ (inj₁ _)) → false
                                     ; (inj₂ (inj₂ q₂′)) → δ₂ q₂ a q₂′ } }
      ; qinit = inj₁ tt
      ; F = λ{ (inj₁ _) → F₁ qinit₁ ∨ F₂ qinit₂
             ; (inj₂ (inj₁ q₁)) → F₁ q₁
             ; (inj₂ (inj₂ q₂)) → F₂ q₂ }
      }

    finite-A∪ : FINITE Q₁ → FINITE Q₂ → FINITE (ND-Automaton.Q A∪)
    finite-A∪ fin₁ fin₂ = finite-⊎ finite-⊤ (finite-⊎ fin₁ fin₂)

  module Kleene2 (A : ND-Automaton Σ) where
    open ND-Automaton A

    A* : ND-Automaton Σ
    A* = record
      { Q = ⊤ ⊎ Q
      ; δ = λ{ (inj₁ tt) a → λ{ (inj₁ _) → false
                               ; (inj₂ q′) → δ qinit a q′ }
             ; (inj₂ q) a → λ{ (inj₁ _) → false
                              ; (inj₂ q′) → δ q a q′ ∨ (F q ∧ δ qinit a q′) } }
      ; qinit = inj₁ tt
      ; F = λ{ (inj₁ _) → true
             ; (inj₂ q) → F q }
      }

    finite-A* : FINITE Q → FINITE (ND-Automaton.Q A*)
    finite-A* = finite-⊎ finite-⊤
