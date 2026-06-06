module Grammar.Leftmost-Derivation where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; _++_; map; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Unary using (_∈_) renaming (_≐′_ to _≐_; _⊆′_ to _⊆_)

open import Language using (Language)
open import Grammar

module _ {Σ : Set} (G : CFG Σ) where
  open CFG G using (N; P; Symbol; _⇒_; _⇒ˡ_; Sentential)
  open Derivation G using (_⇒*_; ⇒*-refl; ⇒*-step)
  open Generated G using (Lang)

  infix 4 _⇒ˡ*_

  terminals : Word Σ → Sentential
  terminals = Grammar.terminals CFG-instance G

  data _⇒ˡ*_ : Sentential → Sentential → Set where
    ⇒ˡ*-refl : ∀ α → α ⇒ˡ* α
    ⇒ˡ*-step : ∀ {α β γ} → α ⇒ˡ β → β ⇒ˡ* γ → α ⇒ˡ* γ

  ⇒ˡ⇒ : ∀ {α β} → α ⇒ˡ β → α ⇒ β
  ⇒ˡ⇒ (u , A , y , v , eq-in , y∈PA , eq-out) =
    map inj₂ u , A , y , v , eq-in , y∈PA , eq-out

  ⇒ˡ*⇒* : ∀ {α β} → α ⇒ˡ* β → α ⇒* β
  ⇒ˡ*⇒* (⇒ˡ*-refl α) = ⇒*-refl α
  ⇒ˡ*⇒* (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) =
    ⇒*-step (⇒ˡ⇒ α⇒ˡβ) (⇒ˡ*⇒* β⇒ˡ*γ)

  ⇒*-length : ∀ {α β} → α ⇒* β → ℕ
  ⇒*-length (⇒*-refl α) = zero
  ⇒*-length (⇒*-step α⇒β β⇒*γ) = suc (⇒*-length β⇒*γ)

  ⇒ˡ*-length : ∀ {α β} → α ⇒ˡ* β → ℕ
  ⇒ˡ*-length (⇒ˡ*-refl α) = zero
  ⇒ˡ*-length (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) = suc (⇒ˡ*-length β⇒ˡ*γ)

  ⇒ˡ*⇒*-length : ∀ {α β} (deriv : α ⇒ˡ* β) → ⇒*-length (⇒ˡ*⇒* deriv) ≡ ⇒ˡ*-length deriv
  ⇒ˡ*⇒*-length (⇒ˡ*-refl α) = refl
  ⇒ˡ*⇒*-length (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) = cong suc (⇒ˡ*⇒*-length β⇒ˡ*γ)

  ⇒ˡ*-trans : ∀ {α β γ} → α ⇒ˡ* β → β ⇒ˡ* γ → α ⇒ˡ* γ
  ⇒ˡ*-trans (⇒ˡ*-refl α) β⇒ˡ*γ = β⇒ˡ*γ
  ⇒ˡ*-trans (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) γ⇒ˡ*δ =
    ⇒ˡ*-step α⇒ˡβ (⇒ˡ*-trans β⇒ˡ*γ γ⇒ˡ*δ)

  terminals-++ : ∀ u v → terminals u ++ terminals v ≡ terminals (u ++ v)
  terminals-++ u v = sym (map-++ inj₂ u v)

  stepˡ-++ʳ : ∀ {α β} γ → α ⇒ˡ β → (α ++ γ) ⇒ˡ (β ++ γ)
  stepˡ-++ʳ γ (u , A , y , v , eq-in , y∈PA , eq-out) =
    u , A , y , v ++ γ
    , trans (cong (_++ γ) eq-in) (++-assoc (terminals u) (inj₁ A ∷ v) γ)
    , y∈PA
    , trans (cong (_++ γ) eq-out)
        (trans (++-assoc (terminals u) (y ++ v) γ)
          (cong (terminals u ++_) (++-assoc y v γ)))

  ⇒ˡ*-++ʳ : ∀ {α β} γ → α ⇒ˡ* β → (α ++ γ) ⇒ˡ* (β ++ γ)
  ⇒ˡ*-++ʳ γ (⇒ˡ*-refl α) = ⇒ˡ*-refl (α ++ γ)
  ⇒ˡ*-++ʳ γ (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) =
    ⇒ˡ*-step (stepˡ-++ʳ γ α⇒ˡβ) (⇒ˡ*-++ʳ γ β⇒ˡ*γ)

  stepˡ-++ˡ-terminals : ∀ u {α β} → α ⇒ˡ β → (terminals u ++ α) ⇒ˡ (terminals u ++ β)
  stepˡ-++ˡ-terminals u (v , A , y , r , eq-in , y∈PA , eq-out) =
    u ++ v , A , y , r
    , trans (cong (terminals u ++_) eq-in)
        (trans (sym (++-assoc (terminals u) (terminals v) (inj₁ A ∷ r)))
          (cong (_++ inj₁ A ∷ r) (sym (map-++ inj₂ u v))))
    , y∈PA
    , trans (cong (terminals u ++_) eq-out)
        (trans (sym (++-assoc (terminals u) (terminals v) (y ++ r)))
          (cong (_++ y ++ r) (sym (map-++ inj₂ u v))))

  ⇒ˡ*-++ˡ-terminals : ∀ u {α β} → α ⇒ˡ* β → (terminals u ++ α) ⇒ˡ* (terminals u ++ β)
  ⇒ˡ*-++ˡ-terminals u (⇒ˡ*-refl α) = ⇒ˡ*-refl (terminals u ++ α)
  ⇒ˡ*-++ˡ-terminals u (⇒ˡ*-step α⇒ˡβ β⇒ˡ*γ) =
    ⇒ˡ*-step (stepˡ-++ˡ-terminals u α⇒ˡβ) (⇒ˡ*-++ˡ-terminals u β⇒ˡ*γ)

  combine-term : ∀ {α β} u v → α ⇒ˡ* terminals u → β ⇒ˡ* terminals v → α ++ β ⇒ˡ* terminals (u ++ v)
  combine-term {α} {β} u v α⇒ˡ*u β⇒ˡ*v =
    subst (λ γ → α ++ β ⇒ˡ* γ) (terminals-++ u v)
      (⇒ˡ*-trans (⇒ˡ*-++ʳ β α⇒ˡ*u) (⇒ˡ*-++ˡ-terminals u β⇒ˡ*v))

  ∷-head : ∀ {A : Set}{x y : A}{xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-head refl = refl

  ∷-tail : ∀ {A : Set}{x y : A}{xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-tail refl = refl

  occurrence : ∀ (α γ₁ : Word Symbol) (A : N) (γ₂ : Word Symbol) →
    α ≡ γ₁ ++ inj₁ A ∷ γ₂ →
    ∃[ u ] ∃[ v ] α ≡ u ++ inj₁ A ∷ v × γ₁ ≡ u × γ₂ ≡ v
  occurrence ε ε A γ₂ ()
  occurrence ε (x ∷ γ₁) A γ₂ ()
  occurrence (inj₁ A ∷ α) ε .A .α refl = ε , α , refl , refl , refl
  occurrence (inj₂ a ∷ α) ε A γ₂ ()
  occurrence (x ∷ α) (y ∷ γ₁) A γ₂ eq
    with occurrence α γ₁ A γ₂ (∷-tail eq)
  ... | u , v , eqα , eqγ₁ , eqγ₂ =
    x ∷ u , v , cong (x ∷_) eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ₁ , eqγ₂

  occurrence-++ : ∀ (α₁ α₂ γ₁ : Word Symbol) (A : N) (γ₂ : Word Symbol) →
    α₁ ++ α₂ ≡ γ₁ ++ inj₁ A ∷ γ₂ →
      (∃[ u ] ∃[ v ] α₁ ≡ u ++ inj₁ A ∷ v × γ₁ ≡ u × γ₂ ≡ v ++ α₂)
    ⊎ (∃[ u ] ∃[ v ] α₂ ≡ u ++ inj₁ A ∷ v × γ₁ ≡ α₁ ++ u × γ₂ ≡ v)
  occurrence-++ ε α₂ γ₁ A γ₂ eq
    with occurrence α₂ γ₁ A γ₂ eq
  ... | u , v , eqα₂ , eqγ₁ , eqγ₂ = inj₂ (u , v , eqα₂ , eqγ₁ , eqγ₂)
  occurrence-++ (inj₁ A ∷ α₁) α₂ ε .A .(α₁ ++ α₂) refl =
    inj₁ (ε , α₁ , refl , refl , refl)
  occurrence-++ (inj₂ a ∷ α₁) α₂ ε A γ₂ ()
  occurrence-++ (x ∷ α₁) α₂ (y ∷ γ₁) A γ₂ eq
    with occurrence-++ α₁ α₂ γ₁ A γ₂ (∷-tail eq)
  ... | inj₁ (u , v , eqα₁ , eqγ₁ , eqγ₂) =
    inj₁ (x ∷ u , v , cong (x ∷_) eqα₁ , cong₂ _∷_ (sym (∷-head eq)) eqγ₁ , eqγ₂)
  ... | inj₂ (u , v , eqα₂ , eqγ₁ , eqγ₂) =
    inj₂ (u , v , eqα₂ , cong₂ _∷_ (sym (∷-head eq)) eqγ₁ , eqγ₂)

  StepSplit : Word Symbol → Word Symbol → Word Symbol → Set
  StepSplit α₁ α₂ β =
      (∃[ β₁ ] β ≡ β₁ ++ α₂ × α₁ ⇒ β₁)
    ⊎ (∃[ β₂ ] β ≡ α₁ ++ β₂ × α₂ ⇒ β₂)

  assoc-left : ∀ (u δ v α₂ : Word Symbol) → u ++ δ ++ v ++ α₂ ≡ (u ++ δ ++ v) ++ α₂
  assoc-left ε δ v α₂ = sym (++-assoc δ v α₂)
  assoc-left (x ∷ u) δ v α₂ = cong (x ∷_) (assoc-left u δ v α₂)

  assoc-right : ∀ (α₁ u δ v : Word Symbol) → (α₁ ++ u) ++ δ ++ v ≡ α₁ ++ u ++ δ ++ v
  assoc-right ε u δ v = refl
  assoc-right (x ∷ α₁) u δ v = cong (x ∷_) (assoc-right α₁ u δ v)

  split-step : ∀ α₁ α₂ β → (α₁ ++ α₂) ⇒ β → StepSplit α₁ α₂ β
  split-step α₁ α₂ β (γ₁ , A , δ , γ₂ , eq-in , δ∈P , eq-out)
    with occurrence-++ α₁ α₂ γ₁ A γ₂ eq-in
  ... | inj₁ (u , v , refl , refl , refl) =
    inj₁ (u ++ δ ++ v , trans eq-out (assoc-left u δ v α₂) , u , A , δ , v , refl , δ∈P , refl)
  ... | inj₂ (u , v , refl , refl , refl) =
    inj₂ (u ++ δ ++ v , trans eq-out (assoc-right α₁ u δ v) , u , A , δ , v , refl , δ∈P , refl)

  SplitDeriv : Word Symbol → Word Symbol → Word Symbol → Set
  SplitDeriv α₁ α₂ β =
    ∃[ β₁ ] ∃[ β₂ ] β ≡ β₁ ++ β₂ × α₁ ⇒* β₁ × α₂ ⇒* β₂

  split-deriv : ∀ α₁ α₂ β → (α₁ ++ α₂) ⇒* β → SplitDeriv α₁ α₂ β
  split-deriv α₁ α₂ β (⇒*-refl α) =
    α₁ , α₂ , refl , ⇒*-refl α₁ , ⇒*-refl α₂
  split-deriv α₁ α₂ γ (⇒*-step {β = β} α⇒β β⇒*γ)
    with split-step α₁ α₂ β α⇒β
  ... | inj₁ (β₁ , refl , α₁⇒β₁)
    with split-deriv β₁ α₂ γ β⇒*γ
  ... | γ₁ , γ₂ , eqγ , β₁⇒*γ₁ , α₂⇒*γ₂ =
    γ₁ , γ₂ , eqγ , ⇒*-step α₁⇒β₁ β₁⇒*γ₁ , α₂⇒*γ₂
  split-deriv α₁ α₂ γ (⇒*-step {β = β} α⇒β β⇒*γ)
    | inj₂ (β₂ , refl , α₂⇒β₂)
    with split-deriv α₁ β₂ γ β⇒*γ
  ... | γ₁ , γ₂ , eqγ , α₁⇒*γ₁ , β₂⇒*γ₂ =
    γ₁ , γ₂ , eqγ , α₁⇒*γ₁ , ⇒*-step α₂⇒β₂ β₂⇒*γ₂

  record SplitDerivLength (α₁ α₂ β : Word Symbol) (deriv : (α₁ ++ α₂) ⇒* β) : Set where
    constructor split-length
    field
      β₁ β₂ : Word Symbol
      β≡β₁β₂ : β ≡ β₁ ++ β₂
      α₁⇒*β₁ : α₁ ⇒* β₁
      α₂⇒*β₂ : α₂ ⇒* β₂
      length-split : ⇒*-length deriv ≡ ⇒*-length α₁⇒*β₁ + ⇒*-length α₂⇒*β₂

  split-deriv-length : ∀ α₁ α₂ β → (deriv : (α₁ ++ α₂) ⇒* β) → SplitDerivLength α₁ α₂ β deriv
  split-deriv-length α₁ α₂ β (⇒*-refl α) =
    split-length α₁ α₂ refl (⇒*-refl α₁) (⇒*-refl α₂) refl
  split-deriv-length α₁ α₂ γ (⇒*-step {β = β} α⇒β β⇒*γ)
    with split-step α₁ α₂ β α⇒β
  ... | inj₁ (β₁ , refl , α₁⇒β₁)
    with split-deriv-length β₁ α₂ γ β⇒*γ
  ... | split-length γ₁ γ₂ eqγ β₁⇒*γ₁ α₂⇒*γ₂ len-eq =
    split-length γ₁ γ₂ eqγ (⇒*-step α₁⇒β₁ β₁⇒*γ₁) α₂⇒*γ₂ (cong suc len-eq)
  split-deriv-length α₁ α₂ γ (⇒*-step {β = β} α⇒β β⇒*γ)
    | inj₂ (β₂ , refl , α₂⇒β₂)
    with split-deriv-length α₁ β₂ γ β⇒*γ
  ... | split-length γ₁ γ₂ eqγ α₁⇒*γ₁ β₂⇒*γ₂ len-eq =
    split-length γ₁ γ₂ eqγ α₁⇒*γ₁ (⇒*-step α₂⇒β₂ β₂⇒*γ₂)
      (trans (cong suc len-eq) (sym (+-suc (⇒*-length α₁⇒*γ₁) (⇒*-length β₂⇒*γ₂))))

  terminal-head : ∀ {a b : Σ} → _≡_ {A = Symbol} (inj₂ a) (inj₂ b) → a ≡ b
  terminal-head refl = refl

  terminal-split : ∀ w β₁ β₂ →
    terminals w ≡ β₁ ++ β₂ →
    ∃[ u ] ∃[ v ] w ≡ u ++ v × β₁ ≡ terminals u × β₂ ≡ terminals v
  terminal-split w ε β₂ eq = ε , w , refl , refl , sym eq
  terminal-split ε (inj₁ A ∷ β₁) β₂ ()
  terminal-split ε (inj₂ a ∷ β₁) β₂ ()
  terminal-split (a ∷ w) (inj₁ A ∷ β₁) β₂ ()
  terminal-split (a ∷ w) (inj₂ b ∷ β₁) β₂ eq
    with terminal-split w β₁ β₂ (∷-tail eq)
  ... | u , v , eqw , eqβ₁ , eqβ₂ =
    a ∷ u , v , cong (a ∷_) eqw
    , cong₂ _∷_ (cong inj₂ (sym (terminal-head (∷-head eq)))) eqβ₁
    , eqβ₂

  no-step-ε : ∀ β → ε ⇒ β → ⊥
  no-step-ε β (ε , A , δ , γ₂ , () , δ∈P , eq-out)
  no-step-ε β (x ∷ γ₁ , A , δ , γ₂ , () , δ∈P , eq-out)

  empty-deriv : ∀ β → ε ⇒* β → β ≡ ε
  empty-deriv .ε (⇒*-refl .ε) = refl
  empty-deriv β (⇒*-step ε⇒β β⇒*γ) = ⊥-elim (no-step-ε _ ε⇒β)

  terminal-step-tail : ∀ a α β → (inj₂ a ∷ α) ⇒ β → ∃[ β′ ] β ≡ inj₂ a ∷ β′ × α ⇒ β′
  terminal-step-tail a α β (ε , A , y , v , () , y∈PA , eq-out)
  terminal-step-tail a α β (inj₁ A₀ ∷ u , A , y , v , () , y∈PA , eq-out)
  terminal-step-tail a .(u ++ inj₁ A ∷ v) .(inj₂ a ∷ u ++ y ++ v)
    (inj₂ .a ∷ u , A , y , v , refl , y∈PA , refl) =
    u ++ y ++ v , refl , u , A , y , v , refl , y∈PA , refl

  terminal-star-tail : ∀ a α w → inj₂ a ∷ α ⇒* terminals w → ∃[ v ] w ≡ a ∷ v × α ⇒* terminals v
  terminal-star-tail a α (.a ∷ v) (⇒*-refl .(inj₂ a ∷ α)) =
    v , refl , ⇒*-refl α
  terminal-star-tail a α w (⇒*-step {β = β} α⇒β β⇒*γ)
    with terminal-step-tail a α β α⇒β
  ... | β′ , refl , α⇒β′
    with terminal-star-tail a β′ w β⇒*γ
  ... | v , eqw , β′⇒*v = v , eqw , ⇒*-step α⇒β′ β′⇒*v

  lemma-eq-++ : ∀ {x y : Symbol} xs ys → [ x ] ≡ xs ++ y ∷ ys → xs ≡ ε × x ≡ y × ys ≡ ε
  lemma-eq-++ ε ys refl = refl , refl , refl
  lemma-eq-++ (x ∷ ε) ys ()
  lemma-eq-++ (x ∷ x₁ ∷ xs) ys ()

  single≢terminals : ∀ A w → [ inj₁ A ] ≢ terminals w
  single≢terminals A ε ()
  single≢terminals A (a ∷ w) ()

  ⇒*-nonrefl-step : ∀ {α β} → α ≢ β → α ⇒* β → ∃[ γ ] α ⇒ γ × γ ⇒* β
  ⇒*-nonrefl-step neq (⇒*-refl α) = ⊥-elim (neq refl)
  ⇒*-nonrefl-step neq (⇒*-step {β = β} α⇒β β⇒*γ) = β , α⇒β , β⇒*γ

  single-step-inversion : ∀ A β → [ inj₁ A ] ⇒ β → ∃[ y ] y ∈ P A × β ≡ y
  single-step-inversion A β (γ₁ , B , y , γ₂ , eq-in , y∈PB , eq-out)
    with lemma-eq-++ γ₁ γ₂ eq-in
  ... | refl , refl , refl = y , y∈PB , trans eq-out (++-identityʳ y)

  {-# TERMINATING #-}
  mutual
    normalize : ∀ α w → α ⇒* terminals w → α ⇒ˡ* terminals w
    normalize ε w deriv =
      subst (λ β → ε ⇒ˡ* β) (sym (empty-deriv (terminals w) deriv)) (⇒ˡ*-refl ε)
    normalize (inj₂ a ∷ α) w deriv
      with terminal-star-tail a α w deriv
    ... | v , refl , α⇒*v = ⇒ˡ*-++ˡ-terminals (a ∷ ε) (normalize α v α⇒*v)
    normalize (inj₁ A ∷ α) w deriv
      with split-deriv [ inj₁ A ] α (terminals w) deriv
    ... | β₁ , β₂ , eqβ , A⇒*β₁ , α⇒*β₂
      with terminal-split w β₁ β₂ eqβ
    ... | u , v , refl , refl , refl =
      combine-term u v (single-normalize A u A⇒*β₁) (normalize α v α⇒*β₂)

    single-normalize : ∀ A w → [ inj₁ A ] ⇒* terminals w → [ inj₁ A ] ⇒ˡ* terminals w
    single-normalize A w deriv
      with ⇒*-nonrefl-step (single≢terminals A w) deriv
    ... | β , A⇒β , β⇒*w
      with single-step-inversion A β A⇒β
    ... | y , y∈PA , β≡y =
      ⇒ˡ*-step
        (ε , A , y , ε , refl , y∈PA , sym (++-identityʳ y))
        (normalize y w (subst (λ γ → γ ⇒* terminals w) β≡y β⇒*w))

  ⇒*terminal⇒⇒ˡ* :
    ∀ w →
    Grammar.start CFG-instance G ⇒* Grammar.terminals CFG-instance G w →
    Grammar.start CFG-instance G ⇒ˡ* Grammar.terminals CFG-instance G w
  ⇒*terminal⇒⇒ˡ* = normalize (Grammar.start CFG-instance G)

  Lang^l : Language Σ
  Lang^l w = Grammar.start CFG-instance G ⇒ˡ* Grammar.terminals CFG-instance G w

  Lang^l⊆Lang : Lang^l ⊆ Lang
  Lang^l⊆Lang w deriv = ⇒ˡ*⇒* deriv

  Lang⊆Lang^l : Lang ⊆ Lang^l
  Lang⊆Lang^l w deriv = ⇒*terminal⇒⇒ˡ* w deriv

  Lang^l≐Lang : Lang^l ≐ Lang
  Lang^l≐Lang = Lang^l⊆Lang , Lang⊆Lang^l
