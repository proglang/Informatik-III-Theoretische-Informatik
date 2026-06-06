module Grammar.DerivationTree where

open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; _++_; [_]; length) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Unary using (_∈_)

open import Language using (Language)
open import Grammar
import Grammar.DerivationHelpers as DerivationHelpers
import Grammar.Leftmost-Derivation as Leftmost-Derivation

module _ {Σ : Set} (G : CFG Σ) where
  open CFG G using (N; S; P; Symbol; _⇒ˡ_)
  open Derivation G using (_⇒*_; ⇒*-refl; ⇒*-step)
  open Leftmost-Derivation using (⇒ˡ*-refl; ⇒ˡ*-step)
  module Helpers = DerivationHelpers.For G
  open Helpers using
    ( terminals
    ; production-step
    ; combine-term
    ; ⇒*-++ˡ
    ; no-stepˡ-ε
    ; terminal-stepˡ-tail
    ; leftmost-head-inversion
    ; single-leftmost-step-inversion
    ; nonterminal-prefix≢terminals
    )

  infix 4 _⇒ˡ*_

  _⇒ˡ*_ : Word Symbol → Word Symbol → Set
  _⇒ˡ*_ = Leftmost-Derivation._⇒ˡ*_ G

  ⇒ˡ*-length : ∀ {α β} → α ⇒ˡ* β → ℕ
  ⇒ˡ*-length = Leftmost-Derivation.⇒ˡ*-length G

  mutual
    data Tree : N → Word Σ → Set where
      node : ∀ {A rhs w} → rhs ∈ P A → Forest rhs w → Tree A w

    data Forest : Word Symbol → Word Σ → Set where
      empty : Forest ε ε
      term : ∀ {a α w} → Forest α w → Forest (inj₂ a ∷ α) (a ∷ w)
      nonterm : ∀ {A α u v} → Tree A u → Forest α v → Forest (inj₁ A ∷ α) (u ++ v)

  DerivationTree : Word Σ → Set
  DerivationTree = Tree S

  Langᵗ : Language Σ
  Langᵗ = DerivationTree

  mutual
    tree⇒derivation : ∀ {A w} → Tree A w → [ inj₁ A ] ⇒* terminals w
    tree⇒derivation (node rhs∈PA forest) =
      ⇒*-step (production-step rhs∈PA) (forest⇒derivation forest)

    forest⇒derivation : ∀ {α w} → Forest α w → α ⇒* terminals w
    forest⇒derivation empty = ⇒*-refl ε
    forest⇒derivation (term {a = a} forest) =
      ⇒*-++ˡ [ inj₂ a ] (forest⇒derivation forest)
    forest⇒derivation (nonterm {u = u} {v = v} tree forest) =
      combine-term u v (tree⇒derivation tree) (forest⇒derivation forest)

  forest-split : ∀ α β w → Forest (α ++ β) w →
    ∃[ u ] ∃[ v ] w ≡ u ++ v × Forest α u × Forest β v
  forest-split ε β w forest = ε , w , refl , empty , forest
  forest-split (inj₂ a ∷ α) β .(a ∷ w) (term {w = w} forest)
    with forest-split α β w forest
  ... | u , v , eqw , forestα , forestβ =
    a ∷ u , v , cong (a ∷_) eqw , term forestα , forestβ
  forest-split (inj₁ A ∷ α) β .(u ++ w) (nonterm {u = u} {v = w} tree forest)
    with forest-split α β w forest
  ... | u′ , v′ , eqw , forestα , forestβ =
    u ++ u′ , v′
    , trans (cong (u ++_) eqw) (sym (++-assoc u u′ v′))
    , nonterm tree forestα
    , forestβ

  empty-leftmost : ∀ β → ε ⇒ˡ* β → β ≡ ε
  empty-leftmost .ε (⇒ˡ*-refl .ε) = refl
  empty-leftmost β (⇒ˡ*-step {β = β′} ε⇒ˡβ′ β′⇒ˡ*β) = ⊥-elim (no-stepˡ-ε β′ ε⇒ˡβ′)

  terminal-leftmost-star-tail : ∀ a α w →
    (inj₂ a ∷ α) ⇒ˡ* terminals w → ∃[ v ] w ≡ a ∷ v × α ⇒ˡ* terminals v
  terminal-leftmost-star-tail a α (.a ∷ v) (⇒ˡ*-refl .(inj₂ a ∷ α)) =
    v , refl , ⇒ˡ*-refl α
  terminal-leftmost-star-tail a α w (⇒ˡ*-step {β = β} α⇒ˡβ β⇒ˡ*γ)
    with terminal-stepˡ-tail a α β α⇒ˡβ
  ... | β′ , refl , α⇒ˡβ′
    with terminal-leftmost-star-tail a β′ w β⇒ˡ*γ
  ... | v , eqw , β′⇒ˡ*v =
    v , eqw , ⇒ˡ*-step α⇒ˡβ′ β′⇒ˡ*v

  record TerminalLeftmostTail a α w (deriv : (inj₂ a ∷ α) ⇒ˡ* terminals w) : Set where
    constructor terminal-leftmost-tail
    field
      v : Word Σ
      w≡a∷v : w ≡ a ∷ v
      tail : α ⇒ˡ* terminals v
      length-tail : ⇒ˡ*-length deriv ≡ ⇒ˡ*-length tail

  terminal-leftmost-star-tail-length : ∀ a α w →
    (deriv : (inj₂ a ∷ α) ⇒ˡ* terminals w) → TerminalLeftmostTail a α w deriv
  terminal-leftmost-star-tail-length a α (.a ∷ v) (⇒ˡ*-refl .(inj₂ a ∷ α)) =
    terminal-leftmost-tail v refl (⇒ˡ*-refl α) refl
  terminal-leftmost-star-tail-length a α w (⇒ˡ*-step {β = β} α⇒ˡβ β⇒ˡ*w)
    with terminal-stepˡ-tail a α β α⇒ˡβ
  ... | β′ , refl , α⇒ˡβ′
    with terminal-leftmost-star-tail-length a β′ w β⇒ˡ*w
  ... | terminal-leftmost-tail v eqw β′⇒ˡ*v len-tail =
    terminal-leftmost-tail v eqw (⇒ˡ*-step α⇒ˡβ′ β′⇒ˡ*v) (cong suc len-tail)

  record NonreflLeftmost {α β : Word Symbol} (deriv : α ⇒ˡ* β) : Set where
    constructor nonrefl-leftmost
    field
      γ : Word Symbol
      first : α ⇒ˡ γ
      rest : γ ⇒ˡ* β
      length-rest : ⇒ˡ*-length deriv ≡ suc (⇒ˡ*-length rest)

  ⇒ˡ*-nonrefl-step : ∀ {α β} → α ≢ β → (deriv : α ⇒ˡ* β) → NonreflLeftmost deriv
  ⇒ˡ*-nonrefl-step neq (⇒ˡ*-refl α) = ⊥-elim (neq refl)
  ⇒ˡ*-nonrefl-step neq (⇒ˡ*-step {β = β} α⇒ˡβ β⇒ˡ*γ) =
    nonrefl-leftmost β α⇒ˡβ β⇒ˡ*γ refl

  mutual
    leftmost⇒tree-fuel : ∀ j {A w} → (deriv : [ inj₁ A ] ⇒ˡ* terminals w) → ⇒ˡ*-length deriv < j → Tree A w
    leftmost⇒tree-fuel zero deriv ()
    leftmost⇒tree-fuel (suc j) {A} {w} deriv deriv<j
      with ⇒ˡ*-nonrefl-step (nonterminal-prefix≢terminals A ε w) deriv
    ... | nonrefl-leftmost β A⇒ˡβ β⇒ˡ*w len-rest
      with subst (λ n → n < suc j) len-rest deriv<j
    ... | s≤s β⇒ˡ*w<j
      with single-leftmost-step-inversion A β A⇒ˡβ
    ... | rhs , rhs∈PA , refl =
      node rhs∈PA
        (leftmost⇒forest-fuel (suc (length rhs)) j ≤-refl β⇒ˡ*w β⇒ˡ*w<j)

    leftmost⇒forest-fuel : ∀ i j {α w} →
      length α < i → (deriv : α ⇒ˡ* terminals w) → ⇒ˡ*-length deriv < j → Forest α w
    leftmost⇒forest-fuel zero j () deriv deriv<j
    leftmost⇒forest-fuel i zero len< deriv ()
    leftmost⇒forest-fuel i (suc j) {α = ε} {w = ε} len< deriv deriv<j = empty
    leftmost⇒forest-fuel i (suc j) {α = ε} {w = a ∷ w} len< deriv deriv<j
      with empty-leftmost (terminals (a ∷ w)) deriv
    ... | ()
    leftmost⇒forest-fuel (suc i) (suc j) {α = inj₂ a ∷ α} {w = w}
      (s≤s lenα<i) deriv deriv<j
      with terminal-leftmost-star-tail-length a α w deriv
    ... | terminal-leftmost-tail v refl α⇒ˡ*v len-tail =
      term
        (leftmost⇒forest-fuel
          i
          (suc j)
          lenα<i
          α⇒ˡ*v
          (subst (λ n → n < suc j) len-tail deriv<j))
    leftmost⇒forest-fuel i (suc j) {α = inj₁ A ∷ α} {w = w} len< deriv deriv<j
      with ⇒ˡ*-nonrefl-step (nonterminal-prefix≢terminals A α w) deriv
    ... | nonrefl-leftmost β Aα⇒ˡβ β⇒ˡ*w len-rest
      with subst (λ n → n < suc j) len-rest deriv<j
    ... | s≤s β⇒ˡ*w<j
      with leftmost-head-inversion A α β Aα⇒ˡβ
    ... | rhs , rhs∈PA , refl
      with leftmost⇒forest-fuel (suc (length (rhs ++ α))) j ≤-refl β⇒ˡ*w β⇒ˡ*w<j
    ... | forest
      with forest-split rhs α w forest
    ... | u , v , refl , forest-rhs , forest-α =
      nonterm (node rhs∈PA forest-rhs) forest-α

  leftmost⇒tree : ∀ {A w} → [ inj₁ A ] ⇒ˡ* terminals w → Tree A w
  leftmost⇒tree deriv =
    leftmost⇒tree-fuel (suc (⇒ˡ*-length deriv)) deriv ≤-refl

  leftmost⇒forest : ∀ {α w} → α ⇒ˡ* terminals w → Forest α w
  leftmost⇒forest {α} deriv =
    leftmost⇒forest-fuel (suc (length α)) (suc (⇒ˡ*-length deriv)) ≤-refl deriv ≤-refl

  derivation⇒tree : ∀ {A w} → [ inj₁ A ] ⇒* terminals w → Tree A w
  derivation⇒tree {A} {w} deriv =
    leftmost⇒tree (Leftmost-Derivation.single-normalize G A w deriv)
