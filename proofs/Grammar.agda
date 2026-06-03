module Grammar where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Unary using (_∈_)

open import Sets using (𝔓)
open import Language using (Language)

contains-NT : ∀ {N Σ : Set} → Word (N ⊎ Σ) → Set
contains-NT ε = ⊥
contains-NT (inj₁ _ ∷ _) = ⊤
contains-NT (inj₂ _ ∷ α) = contains-NT α

record PhraseStructureGrammar (Σ : Set) : Set₁ where
  field
    N : Set
    S : N

  Symbol : Set
  Symbol = N ⊎ Σ

  Sentential : Set
  Sentential = Word Symbol

  field
    P : 𝔓 (Word Symbol × Word Symbol)
    P-lhs-condition : ∀ {α β} → ((α , β) ∈ P) → α ≢ ε × contains-NT {N} {Σ} α

  REG : Set
  REG = ∀ {α β} → ((α , β) ∈ P) → length α ≡ 1 ×
    (β ≡ ε ⊎ ∃[ a ] β ≡ [ inj₂ a ] ⊎ ∃[ a ] ∃[ A ] β ≡ inj₂ a ∷ inj₁ A ∷ ε)

  CFG-property : Set
  CFG-property = ∀ {α β} → ((α , β) ∈ P) → length α ≡ 1

  CNF : Set
  CNF = ∀ {α β} → ((α , β) ∈ P) → length α ≡ 1 ×
    (∃[ a ] β ≡ [ inj₂ a ] ⊎ ∃[ A ] ∃[ B ] β ≡ inj₁ A ∷ inj₁ B ∷ ε)

  CSG : Set
  CSG = ∀ {α β} → ((α , β) ∈ P) → length α ≤ length β
                                  ⊎ α ≡ [ inj₁ S ] × β ≡ ε

  infix 4 _⇒_

  _⇒_ : Sentential → Sentential → Set
  α ⇒ β = ∃[ u ] ∃[ x ] ∃[ y ] ∃[ v ]
    α ≡ u ++ x ++ v
    × ((x , y) ∈ P)
    × β ≡ u ++ y ++ v

record CFG (Σ : Set) : Set₁ where
  field
    N : Set
    S : N

  Symbol : Set
  Symbol = N ⊎ Σ

  field
    P : N → 𝔓 (Word Symbol)

  Sentential : Set
  Sentential = Word Symbol

  infix 4 _⇒_
  -- _⇒*_

  _⇒_ : Sentential → Sentential → Set
  α ⇒ β = ∃[ u ] ∃[ A ] ∃[ y ] ∃[ v ]
    α ≡ u ++ inj₁ A ∷ v
    × (y ∈ P A)
    × β ≡ u ++ y ++ v

record Grammar {Σ : Set} (G : Set₁) : Set₁ where
  field
    N : G → Set
    S : (g : G) → N g

  Symbol : G → Set
  Symbol g = N g ⊎ Σ

  Sentential : G → Set
  Sentential g = Word (Symbol g)

  field
    _⇒_ : (g : G) → Sentential g → Sentential g → Set

  terminals : (g : G) → Word Σ → Sentential g
  terminals g = map inj₂

  start : (g : G) → Sentential g
  start g = inj₁ (S g) ∷ ε

  start≢terminals : ∀ g w → start g ≢ terminals g w
  start≢terminals g ε ()
  start≢terminals g (x₁ ∷ _) ()

instance
  PhraseStructureGrammar-instance : ∀ {Σ} → Grammar {Σ} (PhraseStructureGrammar Σ)
  PhraseStructureGrammar-instance =
    record
      { N = PhraseStructureGrammar.N
      ; S = PhraseStructureGrammar.S
      ; _⇒_ = PhraseStructureGrammar._⇒_
      }

  CFG-instance : ∀ {Σ} → Grammar {Σ} (CFG Σ)
  CFG-instance =
    record
      { N = CFG.N
      ; S = CFG.S
      ; _⇒_ = CFG._⇒_
      }

module _ {Σ : Set} {G : Set₁} ⦃ grammarG : Grammar {Σ} G ⦄ where
  open Grammar grammarG using (Sentential; terminals; start) renaming (_⇒_ to step)

  module Derivation (g : G) where
    infix 4 _⇒*_ _⇒[_]_ _⇒_

    _⇒_ : Sentential g → Sentential g → Set
    _⇒_ = step g

    _⇒[_]_ : Sentential g → ℕ → Sentential g → Set
    α ⇒[ zero ] β = α ≡ β
    α ⇒[ suc n ] β = ∃[ γ ] α ⇒ γ × γ ⇒[ n ] β

    -- _⇒*_ : Sentential g → Sentential g → Set
    -- α ⇒* β = ∃[ n ] α ⇒[ n ] β

    --  ⇒*-refl : ∀ α → α ⇒* α
    -- ⇒*-refl α = zero , refl

    -- ⇒*-step : ∀ {α β γ} → α ⇒ β → β ⇒* γ → α ⇒* γ
    -- ⇒*-step α⇒β (n , β⇒[n]γ) = suc n , (_ , α⇒β , β⇒[n]γ)

    data _⇒*_ : Sentential g → Sentential g → Set where
      ⇒*-refl : ∀ α → α ⇒* α
      ⇒*-step : ∀ {α β γ} → α ⇒ β → β ⇒* γ → α ⇒* γ

  module Generated (g : G) where
    open Derivation g

    Lang : Language Σ
    Lang w = start g ⇒* terminals g w
