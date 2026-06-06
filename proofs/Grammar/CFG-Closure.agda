module Grammar.CFG-Closure where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ; length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; s≤s)
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; ≤-refl; ≤-reflexive; m≤n+m)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Unary using (_∈_; ｛_｝; _∪_) renaming (_≐′_ to _≐_; _⊆′_ to _⊆_)
open import Function using (_∘_)

open import Sets using (𝔓)
open import Language using (Language; 𝟙; _·_; _↑_; _∗)

open import Grammar
import Grammar.Leftmost-Derivation as Leftmost-Derivation

module Union {Σ : Set} where

  mapMaybe : ∀ {X : Set} → Word (Maybe X) → Maybe (Word X)
  mapMaybe ε = just ε
  mapMaybe (nothing ∷ w) = nothing
  mapMaybe (just x ∷ w)
    with mapMaybe w
  ... | just w′ = just (x ∷ w′)
  ... | nothing = nothing

  narrow : ∀ {Ψ Φ : Set} → (Φ → Maybe Ψ) → 𝔓 (Word Ψ) → 𝔓 (Word Φ)
  narrow f inp w
    with mapMaybe (map f w)
  ... | just x = x ∈ inp
  ... | nothing = ⊥

  open CFG
  module _ (G₁ G₂ : CFG Σ) where
    open CFG G₁ renaming (N to N₁; S to S₁; P to P₁; Symbol to Symbol₁; _⇒_ to _⇒₁_)
    open CFG G₂ renaming (N to N₂; S to S₂; P to P₂; Symbol to Symbol₂; _⇒_ to _⇒₂_)


    check₁ : N₁ ⊎ N₂ → Set
    check₁ (inj₁ x) = ⊤
    check₁ (inj₂ y) = ⊥

    check₂ : N₁ ⊎ N₂ → Set
    check₂ (inj₁ x) = ⊥
    check₂ (inj₂ y) = ⊤

    inject₁ : Symbol₁ → (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ
    inject₁ (inj₁ x) = inj₁ (inj₂ (inj₁ x))
    inject₁ (inj₂ a) = inj₂ a

    inject₂ : Symbol₂ → (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ
    inject₂ (inj₁ x) = inj₁ (inj₂ (inj₂ x))
    inject₂ (inj₂ a) = inj₂ a

    project₁ : (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ → Maybe (N₁ ⊎ Σ)
    project₁ (inj₁ (inj₁ tt)) = nothing
    project₁ (inj₁ (inj₂ (inj₁ x))) = just (inj₁ x)
    project₁ (inj₁ (inj₂ (inj₂ y))) = nothing
    project₁ (inj₂ a) = just (inj₂ a)

    project₂ : (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ → Maybe (N₂ ⊎ Σ)
    project₂ (inj₁ (inj₁ tt)) = nothing
    project₂ (inj₁ (inj₂ (inj₁ x))) = nothing
    project₂ (inj₁ (inj₂ (inj₂ y))) = just (inj₁ y)
    project₂ (inj₂ a) = just (inj₂ a)


    G : CFG Σ
    G =
      record
      { N = ⊤ ⊎ (N₁ ⊎ N₂)
      ; S = inj₁ tt
      ; P = productions
      }
      where

        productions : _
        productions (inj₁ tt) = ｛ [ inj₁ (inj₂ (inj₁ S₁)) ]  ｝
                              ∪ ｛ [ inj₁ (inj₂ (inj₂ S₂)) ] ｝
        productions (inj₂ (inj₁ A₁)) = narrow project₁ (P₁ A₁)
        productions (inj₂ (inj₂ A₂)) = narrow project₂ (P₂ A₂)

    open Generated
    open Derivation G
    open Derivation G₁ using () renaming (_⇒*_ to _⇒*₁_)
    open Derivation G₂ using () renaming (_⇒*_ to _⇒*₂_)

    sentential : (N G₁ ⊎ N G₂ → Set) → 𝔓 (Word (Symbol G))
    sentential check ε = ⊤
    sentential check (inj₁ (inj₁ x) ∷ w) = ⊥
    sentential check (inj₁ (inj₂ x) ∷ w) = check x × sentential check w
    sentential check (inj₂ y ∷ w) = sentential check w

    sentential₁ : 𝔓 (Word (Symbol G))
    sentential₁ = sentential check₁

    sentential₁-++ : ∀ α β → sentential₁ (α ++ β) → sentential₁ α × sentential₁ β
    sentential₁-++ ε β sen = tt , sen
    sentential₁-++ (inj₁ (inj₂ (inj₁ x)) ∷ α) β (_ , sen)
      with sentential₁-++ α β sen
    ... | senα , senβ = (tt , senα) , senβ
    sentential₁-++ (inj₂ y ∷ α) β sen
      with sentential₁-++ α β sen
    ... | senα , senβ = senα , senβ

    sentential₁-++⁺ :  ∀ α β → sentential₁ α → sentential₁ β → sentential₁ (α ++ β)
    sentential₁-++⁺ ε β senα senβ = senβ
    sentential₁-++⁺ (inj₁ (inj₂ x) ∷ α) β (cx , senα) senβ = cx , sentential₁-++⁺ α β senα senβ
    sentential₁-++⁺ (inj₂ y ∷ α) β senα senβ = sentential₁-++⁺ α β senα senβ

    sentential₂ : 𝔓 (Word (Symbol G))
    sentential₂ = sentential check₂

    sentential₂-++ : ∀ α β → sentential₂ (α ++ β) → sentential₂ α × sentential₂ β
    sentential₂-++ ε β sen = tt , sen
    sentential₂-++ (inj₁ (inj₂ (inj₂ x)) ∷ α) β (_ , sen)
      with sentential₂-++ α β sen
    ... | senα , senβ = (tt , senα) , senβ
    sentential₂-++ (inj₂ y ∷ α) β sen
      with sentential₂-++ α β sen
    ... | senα , senβ = senα , senβ

    sentential₂-++⁺ :  ∀ α β → sentential₂ α → sentential₂ β → sentential₂ (α ++ β)
    sentential₂-++⁺ ε β senα senβ = senβ
    sentential₂-++⁺ (inj₁ (inj₂ x) ∷ α) β (cx , senα) senβ = cx , sentential₂-++⁺ α β senα senβ
    sentential₂-++⁺ (inj₂ y ∷ α) β senα senβ = sentential₂-++⁺ α β senα senβ

    project-sen₁ : ∀ δ → sentential₁ δ → Word Symbol₁
    project-sen₁ ε sen = ε
    project-sen₁ (inj₁ (inj₁ tt) ∷ δ) ()
    project-sen₁ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (_ , sen) = inj₁ x ∷ project-sen₁ δ sen
    project-sen₁ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (() , sen)
    project-sen₁ (inj₂ y ∷ δ) sen = inj₂ y ∷ project-sen₁ δ sen

    project-sen₂ : ∀ δ → sentential₂ δ → Word Symbol₂
    project-sen₂ ε sen = ε
    project-sen₂ (inj₁ (inj₁ tt) ∷ δ) ()
    project-sen₂ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (() , sen)
    project-sen₂ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (_ , sen) = inj₁ y ∷ project-sen₂ δ sen
    project-sen₂ (inj₂ y ∷ δ) sen = inj₂ y ∷ project-sen₂ δ sen

    inject-project-sen₁ : ∀ δ sen → map inject₁ (project-sen₁ δ sen) ≡ δ
    inject-project-sen₁ ε sen = refl
    inject-project-sen₁ (inj₁ (inj₁ tt) ∷ δ) ()
    inject-project-sen₁ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (_ , sen) = cong (inj₁ (inj₂ (inj₁ x)) ∷_) (inject-project-sen₁ δ sen)
    inject-project-sen₁ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (() , sen)
    inject-project-sen₁ (inj₂ y ∷ δ) sen = cong (inj₂ y ∷_) (inject-project-sen₁ δ sen)

    inject-project-sen₂ : ∀ δ sen → map inject₂ (project-sen₂ δ sen) ≡ δ
    inject-project-sen₂ ε sen = refl
    inject-project-sen₂ (inj₁ (inj₁ tt) ∷ δ) ()
    inject-project-sen₂ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (() , sen)
    inject-project-sen₂ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (_ , sen) = cong (inj₁ (inj₂ (inj₂ y)) ∷_) (inject-project-sen₂ δ sen)
    inject-project-sen₂ (inj₂ y ∷ δ) sen = cong (inj₂ y ∷_) (inject-project-sen₂ δ sen)

    project-sen₁-++ : ∀ α β sen →
      project-sen₁ (α ++ β) sen ≡ project-sen₁ α (sentential₁-++ α β sen .proj₁) ++ project-sen₁ β (sentential₁-++ α β sen .proj₂)
    project-sen₁-++ ε β sen = refl
    project-sen₁-++ (inj₁ (inj₁ tt) ∷ α) β ()
    project-sen₁-++ (inj₁ (inj₂ (inj₁ x)) ∷ α) β (_ , sen) = cong (inj₁ x ∷_) (project-sen₁-++ α β sen)
    project-sen₁-++ (inj₁ (inj₂ (inj₂ y)) ∷ α) β (() , sen)
    project-sen₁-++ (inj₂ y ∷ α) β sen = cong (inj₂ y ∷_) (project-sen₁-++ α β sen)

    project-sen₁-++⁺ : ∀ α β senα senβ →
      project-sen₁ (α ++ β) (sentential₁-++⁺ α β senα senβ) ≡ project-sen₁ α senα ++ project-sen₁ β senβ
    project-sen₁-++⁺ ε β senα senβ = refl
    project-sen₁-++⁺ (inj₁ (inj₂ (inj₁ x)) ∷ α) β (cx , senα) senβ = cong (inj₁ x ∷_) (project-sen₁-++⁺ α β senα senβ)
    project-sen₁-++⁺ (inj₁ (inj₂ (inj₂ y)) ∷ α) β (() , senα) senβ
    project-sen₁-++⁺ (inj₂ y ∷ α) β senα senβ = cong (inj₂ y ∷_) (project-sen₁-++⁺ α β senα senβ)

    project-sen₂-++ : ∀ α β sen →
      project-sen₂ (α ++ β) sen ≡ project-sen₂ α (sentential₂-++ α β sen .proj₁) ++ project-sen₂ β (sentential₂-++ α β sen .proj₂)
    project-sen₂-++ ε β sen = refl
    project-sen₂-++ (inj₁ (inj₁ tt) ∷ α) β ()
    project-sen₂-++ (inj₁ (inj₂ (inj₁ x)) ∷ α) β (() , sen)
    project-sen₂-++ (inj₁ (inj₂ (inj₂ y)) ∷ α) β (_ , sen) = cong (inj₁ y ∷_) (project-sen₂-++ α β sen)
    project-sen₂-++ (inj₂ y ∷ α) β sen = cong (inj₂ y ∷_) (project-sen₂-++ α β sen)

    project-sen₂-++⁺ : ∀ α β senα senβ →
      project-sen₂ (α ++ β) (sentential₂-++⁺ α β senα senβ) ≡ project-sen₂ α senα ++ project-sen₂ β senβ
    project-sen₂-++⁺ ε β senα senβ = refl
    project-sen₂-++⁺ (inj₁ (inj₂ (inj₁ x)) ∷ α) β (() , senα) senβ
    project-sen₂-++⁺ (inj₁ (inj₂ (inj₂ y)) ∷ α) β (cx , senα) senβ = cong (inj₁ y ∷_) (project-sen₂-++⁺ α β senα senβ)
    project-sen₂-++⁺ (inj₂ y ∷ α) β senα senβ = cong (inj₂ y ∷_) (project-sen₂-++⁺ α β senα senβ)

    nothing≢just : ∀ {X : Set} {x : X} → nothing ≢ just x
    nothing≢just ()

    project-sentential-map : ∀ δ δ′ → mapMaybe (map project₁ δ) ≡ just δ′ → sentential₁ δ
    project-sentential-map ε .ε refl = tt
    project-sentential-map (inj₁ (inj₁ tt) ∷ δ) δ′ ()
    project-sentential-map (inj₁ (inj₂ (inj₁ x)) ∷ δ) δ′ eq
      with mapMaybe (map project₁ δ) in eqδ
    ... | just δ″ = tt , project-sentential-map δ δ″ eqδ
    ... | nothing = ⊥-elim (nothing≢just eq)
    project-sentential-map (inj₁ (inj₂ (inj₂ y)) ∷ δ) δ′ ()
    project-sentential-map (inj₂ y ∷ δ) δ′ eq
      with mapMaybe (map project₁ δ) in eqδ
    ... | just δ″ = project-sentential-map δ δ″ eqδ
    ... | nothing = ⊥-elim (nothing≢just eq)

    project-sentential : ∀ δ A₁ → narrow project₁ (P₁ A₁) δ → sentential₁ δ
    project-sentential δ A₁ x
      with mapMaybe (map project₁ δ) in eqδ
    ... | just δ′ = project-sentential-map δ δ′ eqδ
    ... | nothing = ⊥-elim x

    project-sentential₂-map : ∀ δ δ′ → mapMaybe (map project₂ δ) ≡ just δ′ → sentential₂ δ
    project-sentential₂-map ε .ε refl = tt
    project-sentential₂-map (inj₁ (inj₁ tt) ∷ δ) δ′ ()
    project-sentential₂-map (inj₁ (inj₂ (inj₁ x)) ∷ δ) δ′ ()
    project-sentential₂-map (inj₁ (inj₂ (inj₂ y)) ∷ δ) δ′ eq
      with mapMaybe (map project₂ δ) in eqδ
    ... | just δ″ = tt , project-sentential₂-map δ δ″ eqδ
    ... | nothing = ⊥-elim (nothing≢just eq)
    project-sentential₂-map (inj₂ y ∷ δ) δ′ eq
      with mapMaybe (map project₂ δ) in eqδ
    ... | just δ″ = project-sentential₂-map δ δ″ eqδ
    ... | nothing = ⊥-elim (nothing≢just eq)

    project-sentential₂ : ∀ δ A₂ → narrow project₂ (P₂ A₂) δ → sentential₂ δ
    project-sentential₂ δ A₂ x
      with mapMaybe (map project₂ δ) in eqδ
    ... | just δ′ = project-sentential₂-map δ δ′ eqδ
    ... | nothing = ⊥-elim x

    mapMaybe-project₁-sen : ∀ δ sen → mapMaybe (map project₁ δ) ≡ just (project-sen₁ δ sen)
    mapMaybe-project₁-sen ε sen = refl
    mapMaybe-project₁-sen (inj₁ (inj₁ tt) ∷ δ) ()
    mapMaybe-project₁-sen (inj₁ (inj₂ (inj₁ x)) ∷ δ) (_ , sen) rewrite mapMaybe-project₁-sen δ sen = refl
    mapMaybe-project₁-sen (inj₁ (inj₂ (inj₂ y)) ∷ δ) (() , sen)
    mapMaybe-project₁-sen (inj₂ y ∷ δ) sen rewrite mapMaybe-project₁-sen δ sen = refl

    mapMaybe-project₂-sen : ∀ δ sen → mapMaybe (map project₂ δ) ≡ just (project-sen₂ δ sen)
    mapMaybe-project₂-sen ε sen = refl
    mapMaybe-project₂-sen (inj₁ (inj₁ tt) ∷ δ) ()
    mapMaybe-project₂-sen (inj₁ (inj₂ (inj₁ x)) ∷ δ) (() , sen)
    mapMaybe-project₂-sen (inj₁ (inj₂ (inj₂ y)) ∷ δ) (_ , sen) rewrite mapMaybe-project₂-sen δ sen = refl
    mapMaybe-project₂-sen (inj₂ y ∷ δ) sen rewrite mapMaybe-project₂-sen δ sen = refl

    project-production₁ : ∀ δ A₁ → (p : narrow project₁ (P₁ A₁) δ) → (sen : sentential₁ δ) → project-sen₁ δ sen ∈ P₁ A₁
    project-production₁ δ A₁ p sen rewrite mapMaybe-project₁-sen δ sen = p

    project-production₂ : ∀ δ A₂ → (p : narrow project₂ (P₂ A₂) δ) → (sen : sentential₂ δ) → project-sen₂ δ sen ∈ P₂ A₂
    project-production₂ δ A₂ p sen rewrite mapMaybe-project₂-sen δ sen = p

    sen-preserve₁ : ∀ α β → sentential₁ α → (G Derivation.⇒ α) β → sentential₁ β
    sen-preserve₁ α β αin1 (γ₁ , A , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₁-++ γ₁ _ αin1
    sen-preserve₁ .(γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) αin1 (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , refl , A→δ∈P , refl) | sen-γ₁ , tt , sen-γ₂
      using sen-δ ← project-sentential δ A₁ A→δ∈P
      = sentential₁-++⁺ γ₁ (δ ++ γ₂) sen-γ₁ (sentential₁-++⁺ δ γ₂ sen-δ sen-γ₂)

    sen-preserve₁* : ∀ α β → sentential₁ α → α ⇒* β → sentential₁ β
    sen-preserve₁* α β αin1 (Derivation.⇒*-refl α) = αin1
    sen-preserve₁* α γ αin1 (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) = sen-preserve₁* β γ (sen-preserve₁ α β αin1 α⇒β) β⇒*γ

    sen-preserve₂ : ∀ α β → sentential₂ α → (G Derivation.⇒ α) β → sentential₂ β
    sen-preserve₂ α β αin2 (γ₁ , A , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₂-++ γ₁ _ αin2
    sen-preserve₂ .(γ₁ ++ inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) αin2 (γ₁ , inj₂ (inj₂ A₂) , δ , γ₂ , refl , A→δ∈P , refl) | sen-γ₁ , tt , sen-γ₂
      using sen-δ ← project-sentential₂ δ A₂ A→δ∈P
      = sentential₂-++⁺ γ₁ (δ ++ γ₂) sen-γ₁ (sentential₂-++⁺ δ γ₂ sen-δ sen-γ₂)

    sen-preserve₂* : ∀ α β → sentential₂ α → α ⇒* β → sentential₂ β
    sen-preserve₂* α β αin2 (Derivation.⇒*-refl α) = αin2
    sen-preserve₂* α γ αin2 (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) = sen-preserve₂* β γ (sen-preserve₂ α β αin2 α⇒β) β⇒*γ

    sim₁- : ∀ α β → (senα : sentential₁ α) → (step : (G Derivation.⇒ α) β) →
      project-sen₁ α senα ⇒₁ project-sen₁ β (sen-preserve₁ α β senα step)
    sim₁- .(γ₁ ++ inj₁ (inj₁ x) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₁ x , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₁-++ γ₁ (inj₁ (inj₁ x) ∷ γ₂) senα
    ... | sen-γ₁ , ()
    sim₁- .(γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , refl , A→δ∈P , refl)
      = project-sen₁ γ₁ sen-γ₁
      , A₁
      , project-sen₁ δ sen-δ
      , project-sen₁ γ₂ sen-γ₂
      , project-sen₁-++ γ₁ (inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) senα
      , project-production₁ δ A₁ A→δ∈P sen-δ
      , trans (project-sen₁-++⁺ γ₁ (δ ++ γ₂) sen-γ₁ (sentential₁-++⁺ δ γ₂ sen-δ sen-γ₂))
              (cong (project-sen₁ γ₁ sen-γ₁ ++_) (project-sen₁-++⁺ δ γ₂ sen-δ sen-γ₂))
      where
        split = sentential₁-++ γ₁ (inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) senα
        sen-γ₁ = split .proj₁
        sen-γ₂ = split .proj₂ .proj₂
        sen-δ = project-sentential δ A₁ A→δ∈P
    sim₁- .(γ₁ ++ inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₂ A₂) , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₁-++ γ₁ (inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) senα
    ... | sen-γ₁ , (() , sen-γ₂)

    sim₂- : ∀ α β → (senα : sentential₂ α) → (step : (G Derivation.⇒ α) β) →
      project-sen₂ α senα ⇒₂ project-sen₂ β (sen-preserve₂ α β senα step)
    sim₂- .(γ₁ ++ inj₁ (inj₁ x) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₁ x , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₂-++ γ₁ (inj₁ (inj₁ x) ∷ γ₂) senα
    ... | sen-γ₁ , ()
    sim₂- .(γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , refl , A→δ∈P , refl)
      with sentential₂-++ γ₁ (inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) senα
    ... | sen-γ₁ , (() , sen-γ₂)
    sim₂- .(γ₁ ++ inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₂ A₂) , δ , γ₂ , refl , A→δ∈P , refl)
      = project-sen₂ γ₁ sen-γ₁
      , A₂
      , project-sen₂ δ sen-δ
      , project-sen₂ γ₂ sen-γ₂
      , project-sen₂-++ γ₁ (inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) senα
      , project-production₂ δ A₂ A→δ∈P sen-δ
      , trans (project-sen₂-++⁺ γ₁ (δ ++ γ₂) sen-γ₁ (sentential₂-++⁺ δ γ₂ sen-δ sen-γ₂))
              (cong (project-sen₂ γ₁ sen-γ₁ ++_) (project-sen₂-++⁺ δ γ₂ sen-δ sen-γ₂))
      where
        split = sentential₂-++ γ₁ (inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂) senα
        sen-γ₁ = split .proj₁
        sen-γ₂ = split .proj₂ .proj₂
        sen-δ = project-sentential₂ δ A₂ A→δ∈P

    sim₁*- : ∀ α β → (senα : sentential₁ α) → (d : α ⇒* β) →
      project-sen₁ α senα ⇒*₁ project-sen₁ β (sen-preserve₁* α β senα d)
    sim₁*- α β senα (Derivation.⇒*-refl α) = Derivation.⇒*-refl (project-sen₁ α senα)
    sim₁*- α γ senα (Derivation.⇒*-step {β = β} α⇒β β⇒*γ)
      = Derivation.⇒*-step (sim₁- α β senα α⇒β) (sim₁*- β γ (sen-preserve₁ α β senα α⇒β) β⇒*γ)

    sim₂*- : ∀ α β → (senα : sentential₂ α) → (d : α ⇒* β) →
      project-sen₂ α senα ⇒*₂ project-sen₂ β (sen-preserve₂* α β senα d)
    sim₂*- α β senα (Derivation.⇒*-refl α) = Derivation.⇒*-refl (project-sen₂ α senα)
    sim₂*- α γ senα (Derivation.⇒*-step {β = β} α⇒β β⇒*γ)
      = Derivation.⇒*-step (sim₂- α β senα α⇒β) (sim₂*- β γ (sen-preserve₂ α β senα α⇒β) β⇒*γ)

    inject-project₁-map : ∀ δ → mapMaybe (map project₁ (map inject₁ δ)) ≡ just δ
    inject-project₁-map ε = refl
    inject-project₁-map (inj₁ x ∷ δ) rewrite inject-project₁-map δ = refl
    inject-project₁-map (inj₂ y ∷ δ) rewrite inject-project₁-map δ = refl

    inject-project₁ : ∀ {X : 𝔓 (Word (N₁ ⊎ Σ))} δ → δ ∈ X → map inject₁ δ ∈ narrow project₁ X
    inject-project₁ δ δ∈X rewrite inject-project₁-map δ = δ∈X

    inject-terminals : ∀ α₁ → map inject₁ (Grammar.terminals CFG-instance G₁ α₁) ≡ Grammar.terminals CFG-instance G α₁
    inject-terminals ε = refl
    inject-terminals (x ∷ α₁) = cong (inj₂ x ∷_) (inject-terminals α₁)

    sim₁ : ∀ α₁ β₁ → α₁ ⇒₁ β₁ → (G Derivation.⇒ map inject₁ α₁) (map inject₁ β₁)
    sim₁ α₁ β₁ (γ₁ , A₁ , δ₁ , γ₂ , refl , δ₁∈P₁A₁ , refl)
      = map inject₁ γ₁
      , inj₂ (inj₁ A₁)
      , map inject₁ δ₁
      , (map inject₁ γ₂)
      , map-++ inject₁ γ₁ (inj₁ A₁ ∷ γ₂)
      , inject-project₁ δ₁ δ₁∈P₁A₁ 
      , trans (map-++ inject₁ γ₁ (δ₁ ++ γ₂))
              (cong (map inject₁ γ₁ ++_) (map-++ inject₁ δ₁ γ₂))

    sim₁* : ∀ α₁ β₁ → α₁ ⇒*₁ β₁ → map inject₁ α₁ ⇒* map inject₁ β₁
    sim₁* α₁ β₁ (Derivation.⇒*-refl α) = ⇒*-refl (map inject₁ α₁)
    sim₁* α₁ β₁ (Derivation.⇒*-step {β = β} α₁⇒β β⇒*β₁)
      = ⇒*-step (sim₁ α₁ β α₁⇒β) (sim₁* _ _ β⇒*β₁)

    inject-project₂-map : ∀ δ → mapMaybe (map project₂ (map inject₂ δ)) ≡ just δ
    inject-project₂-map ε = refl
    inject-project₂-map (inj₁ x ∷ δ) rewrite inject-project₂-map δ = refl
    inject-project₂-map (inj₂ y ∷ δ) rewrite inject-project₂-map δ = refl

    inject-project₂ : ∀ {X : 𝔓 (Word (N₂ ⊎ Σ))} δ → δ ∈ X → map inject₂ δ ∈ narrow project₂ X
    inject-project₂ δ δ∈X rewrite inject-project₂-map δ = δ∈X

    inject-terminals₂ : ∀ α₂ → map inject₂ (Grammar.terminals CFG-instance G₂ α₂) ≡ Grammar.terminals CFG-instance G α₂
    inject-terminals₂ ε = refl
    inject-terminals₂ (x ∷ α₂) = cong (inj₂ x ∷_) (inject-terminals₂ α₂)

    sim₂ : ∀ α₂ β₂ → α₂ ⇒₂ β₂ → (G Derivation.⇒ map inject₂ α₂) (map inject₂ β₂)
    sim₂ α₂ β₂ (γ₁ , A₂ , δ₂ , γ₂ , refl , δ₂∈P₂A₂ , refl)
      = map inject₂ γ₁
      , inj₂ (inj₂ A₂)
      , map inject₂ δ₂
      , map inject₂ γ₂
      , map-++ inject₂ γ₁ (inj₁ A₂ ∷ γ₂)
      , inject-project₂ δ₂ δ₂∈P₂A₂
      , trans (map-++ inject₂ γ₁ (δ₂ ++ γ₂))
              (cong (map inject₂ γ₁ ++_) (map-++ inject₂ δ₂ γ₂))

    sim₂* : ∀ α₂ β₂ → α₂ ⇒*₂ β₂ → map inject₂ α₂ ⇒* map inject₂ β₂
    sim₂* α₂ β₂ (Derivation.⇒*-refl α) = ⇒*-refl (map inject₂ α₂)
    sim₂* α₂ β₂ (Derivation.⇒*-step {β = β} α₂⇒β β⇒*β₂)
      = ⇒*-step (sim₂ α₂ β α₂⇒β) (sim₂* _ _ β⇒*β₂)

    project-sen₁-terminals : ∀ w sen → project-sen₁ (Grammar.terminals CFG-instance G w) sen ≡ Grammar.terminals CFG-instance G₁ w
    project-sen₁-terminals ε sen = refl
    project-sen₁-terminals (a ∷ w) sen = cong (inj₂ a ∷_) (project-sen₁-terminals w sen)

    project-sen₂-terminals : ∀ w sen → project-sen₂ (Grammar.terminals CFG-instance G w) sen ≡ Grammar.terminals CFG-instance G₂ w
    project-sen₂-terminals ε sen = refl
    project-sen₂-terminals (a ∷ w) sen = cong (inj₂ a ∷_) (project-sen₂-terminals w sen)

    private
      lemma-eq-++ : ∀ {A : Set}{x y : A} xs ys → [ x ] ≡ xs ++ y ∷ ys → xs ≡ ε × x ≡ y × ys ≡ ε
      lemma-eq-++ ε ys refl = refl , refl , refl
      lemma-eq-++ (x ∷ ε) ys ()
      lemma-eq-++ (x ∷ x₁ ∷ xs) ys ()

    start-step-inversion : ∀ β → (G Derivation.⇒ Grammar.start CFG-instance G) β →
      (β ≡ [ inj₁ (inj₂ (inj₁ S₁)) ]) ⊎ (β ≡ [ inj₁ (inj₂ (inj₂ S₂)) ])
    start-step-inversion β (γ₁ , A , δ , γ₂ , eq-in , δ∈PA , eq-out)
      with lemma-eq-++ γ₁ γ₂ eq-in
    ... | refl , refl , refl with δ∈PA | eq-out
    ... | inj₁ refl | refl = inj₁ refl
    ... | inj₂ refl | refl = inj₂ refl

    ⇒*-nonrefl-step : ∀ {α β} → α ≢ β → α ⇒* β → ∃[ γ ] (G Derivation.⇒ α) γ × γ ⇒* β
    ⇒*-nonrefl-step neq (Derivation.⇒*-refl α) = ⊥-elim (neq refl)
    ⇒*-nonrefl-step neq (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) = β , α⇒β , β⇒*γ

    correct-left : Lang G ⊆ (Lang G₁) ∪ (Lang G₂)
    correct-left w deriv
      with ⇒*-nonrefl-step (Grammar.start≢terminals CFG-instance G w) deriv
    ... | β , start⇒β , β⇒*w
      with start-step-inversion β start⇒β
    ... | inj₁ refl =
      inj₁
        (subst (λ γ → Grammar.start CFG-instance G₁ ⇒*₁ γ)
          (project-sen₁-terminals w (sen-preserve₁* _ _ (tt , tt) β⇒*w))
          (sim₁*- _ _ (tt , tt) β⇒*w))
    ... | inj₂ refl =
      inj₂
        (subst (λ γ → Grammar.start CFG-instance G₂ ⇒*₂ γ)
          (project-sen₂-terminals w (sen-preserve₂* _ _ (tt , tt) β⇒*w))
          (sim₂*- _ _ (tt , tt) β⇒*w))

    correct-right : (Lang G₁) ∪ (Lang G₂) ⊆ Lang G
    correct-right w (inj₁ w∈L₁)
      = Derivation.⇒*-step
        (ε , S G , [ inj₁ (inj₂ (inj₁ S₁)) ] , ε , refl , (inj₁ refl) , refl)
        (subst (_ ⇒*_) (inject-terminals _) (sim₁* _ _ w∈L₁) )
    correct-right w (inj₂ w∈L₂)
      = Derivation.⇒*-step
        ((ε , S G , [ inj₁ (inj₂ (inj₂ S₂)) ] , ε , refl , (inj₂ refl) , refl))
        (subst (_ ⇒*_) (inject-terminals₂ _) (sim₂* _ _ w∈L₂))
    

    correct : Lang G ≐ (Lang G₁) ∪ (Lang G₂)
    correct = correct-left , correct-right

module Concatenation {Σ : Set} where

  module U = Union {Σ}

  open CFG using (S; Symbol)
  module _ (G₁ G₂ : CFG Σ) where
    open CFG G₁ renaming (N to N₁; S to S₁; P to P₁; Symbol to Symbol₁; _⇒_ to _⇒₁_)
    open CFG G₂ renaming (N to N₂; S to S₂; P to P₂; Symbol to Symbol₂; _⇒_ to _⇒₂_)

    inject₁ : Symbol₁ → (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ
    inject₁ (inj₁ x) = inj₁ (inj₂ (inj₁ x))
    inject₁ (inj₂ a) = inj₂ a

    inject₂ : Symbol₂ → (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ
    inject₂ (inj₁ x) = inj₁ (inj₂ (inj₂ x))
    inject₂ (inj₂ a) = inj₂ a

    project₁ : (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ → Maybe (N₁ ⊎ Σ)
    project₁ (inj₁ (inj₁ tt)) = nothing
    project₁ (inj₁ (inj₂ (inj₁ x))) = just (inj₁ x)
    project₁ (inj₁ (inj₂ (inj₂ y))) = nothing
    project₁ (inj₂ a) = just (inj₂ a)

    project₂ : (⊤ ⊎ N₁ ⊎ N₂) ⊎ Σ → Maybe (N₂ ⊎ Σ)
    project₂ (inj₁ (inj₁ tt)) = nothing
    project₂ (inj₁ (inj₂ (inj₁ x))) = nothing
    project₂ (inj₁ (inj₂ (inj₂ y))) = just (inj₁ y)
    project₂ (inj₂ a) = just (inj₂ a)

    inject-project-sen₁ : ∀ δ sen → map inject₁ (U.project-sen₁ G₁ G₂ δ sen) ≡ δ
    inject-project-sen₁ ε sen = refl
    inject-project-sen₁ (inj₁ (inj₁ tt) ∷ δ) ()
    inject-project-sen₁ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (_ , sen) = cong (inj₁ (inj₂ (inj₁ x)) ∷_) (inject-project-sen₁ δ sen)
    inject-project-sen₁ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (() , sen)
    inject-project-sen₁ (inj₂ y ∷ δ) sen = cong (inj₂ y ∷_) (inject-project-sen₁ δ sen)

    inject-project-sen₂ : ∀ δ sen → map inject₂ (U.project-sen₂ G₁ G₂ δ sen) ≡ δ
    inject-project-sen₂ ε sen = refl
    inject-project-sen₂ (inj₁ (inj₁ tt) ∷ δ) ()
    inject-project-sen₂ (inj₁ (inj₂ (inj₁ x)) ∷ δ) (() , sen)
    inject-project-sen₂ (inj₁ (inj₂ (inj₂ y)) ∷ δ) (_ , sen) = cong (inj₁ (inj₂ (inj₂ y)) ∷_) (inject-project-sen₂ δ sen)
    inject-project-sen₂ (inj₂ y ∷ δ) sen = cong (inj₂ y ∷_) (inject-project-sen₂ δ sen)

    G : CFG Σ
    G =
      record
      { N = ⊤ ⊎ (N₁ ⊎ N₂)
      ; S = inj₁ tt
      ; P = productions
      }
      where
        productions : _
        productions (inj₁ tt) = ｛ map inject₁ (Grammar.start CFG-instance G₁) ++ map inject₂ (Grammar.start CFG-instance G₂) ｝
        productions (inj₂ (inj₁ A₁)) = U.narrow (U.project₁ G₁ G₂) (P₁ A₁)
        productions (inj₂ (inj₂ A₂)) = U.narrow (U.project₂ G₁ G₂) (P₂ A₂)

    open Generated
    open Derivation G
    open Derivation G₁ using () renaming (_⇒*_ to _⇒*₁_)
    open Derivation G₂ using () renaming (_⇒*_ to _⇒*₂_)

    private
      lemma-eq-++ : ∀ {A : Set}{x y : A} xs ys → [ x ] ≡ xs ++ y ∷ ys → xs ≡ ε × x ≡ y × ys ≡ ε
      lemma-eq-++ ε ys refl = refl , refl , refl
      lemma-eq-++ (x ∷ ε) ys ()
      lemma-eq-++ (x ∷ x₁ ∷ xs) ys ()

    no-start : Word (Symbol G) → Set
    no-start ε = ⊤
    no-start (inj₁ (inj₁ tt) ∷ α) = ⊥
    no-start (inj₁ (inj₂ x) ∷ α) = no-start α
    no-start (inj₂ a ∷ α) = no-start α

    no-start-++ : ∀ α β → no-start α → no-start β → no-start (α ++ β)
    no-start-++ ε β nsα nsβ = nsβ
    no-start-++ (inj₁ (inj₁ tt) ∷ α) β () nsβ
    no-start-++ (inj₁ (inj₂ x) ∷ α) β nsα nsβ = no-start-++ α β nsα nsβ
    no-start-++ (inj₂ a ∷ α) β nsα nsβ = no-start-++ α β nsα nsβ

    no-start-map₁ : ∀ α₁ → no-start (map inject₁ α₁)
    no-start-map₁ ε = tt
    no-start-map₁ (inj₁ A₁ ∷ α₁) = no-start-map₁ α₁
    no-start-map₁ (inj₂ a ∷ α₁) = no-start-map₁ α₁

    no-start-map₂ : ∀ α₂ → no-start (map inject₂ α₂)
    no-start-map₂ ε = tt
    no-start-map₂ (inj₁ A₂ ∷ α₂) = no-start-map₂ α₂
    no-start-map₂ (inj₂ a ∷ α₂) = no-start-map₂ α₂

    start-in-context : ∀ γ₁ γ₂ → no-start (γ₁ ++ inj₁ (inj₁ tt) ∷ γ₂) → ⊥
    start-in-context ε γ₂ ns = ns
    start-in-context (inj₁ (inj₁ tt) ∷ γ₁) γ₂ ()
    start-in-context (inj₁ (inj₂ x) ∷ γ₁) γ₂ ns = start-in-context γ₁ γ₂ ns
    start-in-context (inj₂ a ∷ γ₁) γ₂ ns = start-in-context γ₁ γ₂ ns

    no-start-split : ∀ α₁ α₂ γ₁ γ₂ →
      map inject₁ α₁ ++ map inject₂ α₂ ≢ γ₁ ++ inj₁ (inj₁ tt) ∷ γ₂
    no-start-split α₁ α₂ γ₁ γ₂ eq =
      start-in-context γ₁ γ₂
        (subst no-start eq (no-start-++ (map inject₁ α₁) (map inject₂ α₂) (no-start-map₁ α₁) (no-start-map₂ α₂)))

    no-left : Word (Symbol G) → Set
    no-left ε = ⊤
    no-left (inj₁ (inj₁ tt) ∷ α) = no-left α
    no-left (inj₁ (inj₂ (inj₁ A₁)) ∷ α) = ⊥
    no-left (inj₁ (inj₂ (inj₂ A₂)) ∷ α) = no-left α
    no-left (inj₂ a ∷ α) = no-left α

    no-left-map₂ : ∀ α₂ → no-left (map inject₂ α₂)
    no-left-map₂ ε = tt
    no-left-map₂ (inj₁ A₂ ∷ α₂) = no-left-map₂ α₂
    no-left-map₂ (inj₂ a ∷ α₂) = no-left-map₂ α₂

    left-in-context : ∀ γ₁ A₁ γ₂ → no-left (γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) → ⊥
    left-in-context ε A₁ γ₂ ns = ns
    left-in-context (inj₁ (inj₁ tt) ∷ γ₁) A₁ γ₂ ns = left-in-context γ₁ A₁ γ₂ ns
    left-in-context (inj₁ (inj₂ (inj₁ A)) ∷ γ₁) A₁ γ₂ ()
    left-in-context (inj₁ (inj₂ (inj₂ A)) ∷ γ₁) A₁ γ₂ ns = left-in-context γ₁ A₁ γ₂ ns
    left-in-context (inj₂ a ∷ γ₁) A₁ γ₂ ns = left-in-context γ₁ A₁ γ₂ ns

    no-left-inject₂ : ∀ α₂ γ₁ A₁ γ₂ →
      map inject₂ α₂ ≢ γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂
    no-left-inject₂ α₂ γ₁ A₁ γ₂ eq =
      left-in-context γ₁ A₁ γ₂ (subst no-left eq (no-left-map₂ α₂))

    ∷-head : ∀ {A : Set}{x y : A}{xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
    ∷-head refl = refl

    ∷-tail : ∀ {A : Set}{x y : A}{xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
    ∷-tail refl = refl

    left-occurrence : ∀ α₁ α₂ γ₁ A₁ γ₂ →
      map inject₁ α₁ ++ map inject₂ α₂ ≡ γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂ →
      ∃[ u ] ∃[ v ] α₁ ≡ u ++ inj₁ A₁ ∷ v
        × γ₁ ≡ map inject₁ u
        × γ₂ ≡ map inject₁ v ++ map inject₂ α₂
    left-occurrence ε α₂ γ₁ A₁ γ₂ eq = ⊥-elim (no-left-inject₂ α₂ γ₁ A₁ γ₂ eq)
    left-occurrence (inj₁ A₁ ∷ α₁) α₂ ε .A₁ .(map inject₁ α₁ ++ map inject₂ α₂) refl =
      ε , α₁ , refl , refl , refl
    left-occurrence (inj₂ a ∷ α₁) α₂ ε A₁ γ₂ ()
    left-occurrence (inj₁ A ∷ α₁) α₂ (y ∷ γ₁) A₁ γ₂ eq
      with left-occurrence α₁ α₂ γ₁ A₁ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      inj₁ A ∷ u , v , cong (inj₁ A ∷_) eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂
    left-occurrence (inj₂ a ∷ α₁) α₂ (y ∷ γ₁) A₁ γ₂ eq
      with left-occurrence α₁ α₂ γ₁ A₁ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      inj₂ a ∷ u , v , cong (inj₂ a ∷_) eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂

    right-occurrence : ∀ α₁ α₂ γ₁ A₂ γ₂ →
      map inject₁ α₁ ++ map inject₂ α₂ ≡ γ₁ ++ inj₁ (inj₂ (inj₂ A₂)) ∷ γ₂ →
      ∃[ u ] ∃[ v ] α₂ ≡ u ++ inj₁ A₂ ∷ v
        × γ₁ ≡ map inject₁ α₁ ++ map inject₂ u
        × γ₂ ≡ map inject₂ v
    right-occurrence (inj₁ A₁ ∷ α₁) α₂ ε A₂ γ₂ ()
    right-occurrence (inj₂ a ∷ α₁) α₂ ε A₂ γ₂ ()
    right-occurrence (inj₁ A₁ ∷ α₁) α₂ (y ∷ γ₁) A₂ γ₂ eq
      with right-occurrence α₁ α₂ γ₁ A₂ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      u , v , eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂
    right-occurrence (inj₂ a ∷ α₁) α₂ (y ∷ γ₁) A₂ γ₂ eq
      with right-occurrence α₁ α₂ γ₁ A₂ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      u , v , eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂
    right-occurrence ε ε ε A₂ γ₂ ()
    right-occurrence ε ε (x ∷ γ₁) A₂ γ₂ ()
    right-occurrence ε (inj₁ A₂ ∷ α₂) ε .A₂ .(map inject₂ α₂) refl =
      ε , α₂ , refl , refl , refl
    right-occurrence ε (inj₂ a ∷ α₂) ε A₂ γ₂ ()
    right-occurrence ε (inj₁ A ∷ α₂) (y ∷ γ₁) A₂ γ₂ eq
      with right-occurrence ε α₂ γ₁ A₂ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      inj₁ A ∷ u , v , cong (inj₁ A ∷_) eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂
    right-occurrence ε (inj₂ a ∷ α₂) (y ∷ γ₁) A₂ γ₂ eq
      with right-occurrence ε α₂ γ₁ A₂ γ₂ (∷-tail eq)
    ... | u , v , eqα , eqγ , eqγ₂ =
      inj₂ a ∷ u , v , cong (inj₂ a ∷_) eqα , cong₂ _∷_ (sym (∷-head eq)) eqγ , eqγ₂

    StepSplit : Word Symbol₁ → Word Symbol₂ → Word (Symbol G) → Set
    StepSplit α₁ α₂ β =
        (∃[ β₁ ] β ≡ map inject₁ β₁ ++ map inject₂ α₂ × α₁ ⇒₁ β₁)
      ⊎ (∃[ β₂ ] β ≡ map inject₁ α₁ ++ map inject₂ β₂ × α₂ ⇒₂ β₂)

    map-inject₁-++₃ : ∀ u δ v α₂ →
      map inject₁ u ++ map inject₁ δ ++ map inject₁ v ++ map inject₂ α₂
      ≡ map inject₁ (u ++ δ ++ v) ++ map inject₂ α₂
    map-inject₁-++₃ ε ε v α₂ = refl
    map-inject₁-++₃ ε (x ∷ δ) v α₂ = cong (inject₁ x ∷_) (map-inject₁-++₃ ε δ v α₂)
    map-inject₁-++₃ (x ∷ u) δ v α₂ = cong (inject₁ x ∷_) (map-inject₁-++₃ u δ v α₂)

    map-inject₂-++₂ : ∀ u δ v →
      map inject₂ u ++ map inject₂ δ ++ map inject₂ v
      ≡ map inject₂ (u ++ δ ++ v)
    map-inject₂-++₂ ε ε v = refl
    map-inject₂-++₂ ε (x ∷ δ) v = cong (inject₂ x ∷_) (map-inject₂-++₂ ε δ v)
    map-inject₂-++₂ (x ∷ u) δ v = cong (inject₂ x ∷_) (map-inject₂-++₂ u δ v)

    map-inject₂-++₃ : ∀ α₁ u δ v →
      (map inject₁ α₁ ++ map inject₂ u) ++ map inject₂ δ ++ map inject₂ v
      ≡ map inject₁ α₁ ++ map inject₂ (u ++ δ ++ v)
    map-inject₂-++₃ ε u δ v = map-inject₂-++₂ u δ v
    map-inject₂-++₃ (x ∷ α₁) u δ v = cong (inject₁ x ∷_) (map-inject₂-++₃ α₁ u δ v)

    left-segment-eq-ε : ∀ δ v α₂ senδ →
      δ ++ map inject₁ v ++ map inject₂ α₂
      ≡ map inject₁ (U.project-sen₁ G₁ G₂ δ senδ ++ v) ++ map inject₂ α₂
    left-segment-eq-ε ε v α₂ senδ = refl
    left-segment-eq-ε (inj₁ (inj₁ tt) ∷ δ) v α₂ ()
    left-segment-eq-ε (inj₁ (inj₂ (inj₁ A₁)) ∷ δ) v α₂ (_ , senδ) =
      cong (inj₁ (inj₂ (inj₁ A₁)) ∷_) (left-segment-eq-ε δ v α₂ senδ)
    left-segment-eq-ε (inj₁ (inj₂ (inj₂ A₂)) ∷ δ) v α₂ (() , senδ)
    left-segment-eq-ε (inj₂ a ∷ δ) v α₂ senδ =
      cong (inj₂ a ∷_) (left-segment-eq-ε δ v α₂ senδ)

    left-segment-eq : ∀ u δ v α₂ senδ →
      map inject₁ u ++ δ ++ map inject₁ v ++ map inject₂ α₂
      ≡ map inject₁ (u ++ U.project-sen₁ G₁ G₂ δ senδ ++ v) ++ map inject₂ α₂
    left-segment-eq ε δ v α₂ senδ = left-segment-eq-ε δ v α₂ senδ
    left-segment-eq (x ∷ u) δ v α₂ senδ =
      cong (inject₁ x ∷_) (left-segment-eq u δ v α₂ senδ)

    right-segment-eq-ε : ∀ u δ v senδ →
      map inject₂ u ++ δ ++ map inject₂ v
      ≡ map inject₂ (u ++ U.project-sen₂ G₁ G₂ δ senδ ++ v)
    right-segment-eq-ε ε ε v senδ = refl
    right-segment-eq-ε ε (inj₁ (inj₁ tt) ∷ δ) v ()
    right-segment-eq-ε ε (inj₁ (inj₂ (inj₁ A₁)) ∷ δ) v (() , senδ)
    right-segment-eq-ε ε (inj₁ (inj₂ (inj₂ A₂)) ∷ δ) v (_ , senδ) =
      cong (inj₁ (inj₂ (inj₂ A₂)) ∷_) (right-segment-eq-ε ε δ v senδ)
    right-segment-eq-ε ε (inj₂ a ∷ δ) v senδ =
      cong (inj₂ a ∷_) (right-segment-eq-ε ε δ v senδ)
    right-segment-eq-ε (x ∷ u) δ v senδ =
      cong (inject₂ x ∷_) (right-segment-eq-ε u δ v senδ)

    right-segment-eq : ∀ α₁ u δ v senδ →
      (map inject₁ α₁ ++ map inject₂ u) ++ δ ++ map inject₂ v
      ≡ map inject₁ α₁ ++ map inject₂ (u ++ U.project-sen₂ G₁ G₂ δ senδ ++ v)
    right-segment-eq ε u δ v senδ = right-segment-eq-ε u δ v senδ
    right-segment-eq (x ∷ α₁) u δ v senδ =
      cong (inject₁ x ∷_) (right-segment-eq α₁ u δ v senδ)

    split-step : ∀ α₁ α₂ β → (map inject₁ α₁ ++ map inject₂ α₂) ⇒ β → StepSplit α₁ α₂ β
    split-step α₁ α₂ β (γ₁ , inj₁ tt , δ , γ₂ , eq-in , δ∈P , eq-out) =
      ⊥-elim (no-start-split α₁ α₂ γ₁ γ₂ eq-in)
    split-step α₁ α₂ β (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , eq-in , δ∈P , eq-out)
      with left-occurrence α₁ α₂ γ₁ A₁ γ₂ eq-in
    ... | u , v , refl , refl , refl
      with U.project-sentential G₁ G₂ δ A₁ δ∈P
    ... | senδ
      = inj₁
        ( u ++ U.project-sen₁ G₁ G₂ δ senδ ++ v
        , trans eq-out (left-segment-eq u δ v α₂ senδ)
        , u , A₁ , U.project-sen₁ G₁ G₂ δ senδ , v , refl
        , U.project-production₁ G₁ G₂ δ A₁ δ∈P senδ
        , refl)
    split-step α₁ α₂ β (γ₁ , inj₂ (inj₂ A₂) , δ , γ₂ , eq-in , δ∈P , eq-out)
      with right-occurrence α₁ α₂ γ₁ A₂ γ₂ eq-in
    ... | u , v , refl , refl , refl
      with U.project-sentential₂ G₁ G₂ δ A₂ δ∈P
    ... | senδ
      = inj₂
        ( u ++ U.project-sen₂ G₁ G₂ δ senδ ++ v
        , trans eq-out (right-segment-eq α₁ u δ v senδ)
        , u , A₂ , U.project-sen₂ G₁ G₂ δ senδ , v , refl
        , U.project-production₂ G₁ G₂ δ A₂ δ∈P senδ
        , refl)

    SplitDeriv : Word Symbol₁ → Word Symbol₂ → Word (Symbol G) → Set
    SplitDeriv α₁ α₂ β =
      ∃[ β₁ ] ∃[ β₂ ] β ≡ map inject₁ β₁ ++ map inject₂ β₂ × α₁ ⇒*₁ β₁ × α₂ ⇒*₂ β₂

    split-deriv : ∀ α₁ α₂ β → (map inject₁ α₁ ++ map inject₂ α₂) ⇒* β → SplitDeriv α₁ α₂ β
    split-deriv α₁ α₂ β (Derivation.⇒*-refl α) =
      α₁ , α₂ , refl , Derivation.⇒*-refl α₁ , Derivation.⇒*-refl α₂
    split-deriv α₁ α₂ γ (Derivation.⇒*-step {β = β} α⇒β β⇒*γ)
      with split-step α₁ α₂ β α⇒β
    ... | inj₁ (β₁ , refl , α₁⇒β₁)
      with split-deriv β₁ α₂ γ β⇒*γ
    ... | γ₁ , γ₂ , eqγ , β₁⇒*γ₁ , α₂⇒*γ₂ =
      γ₁ , γ₂ , eqγ , Derivation.⇒*-step α₁⇒β₁ β₁⇒*γ₁ , α₂⇒*γ₂
    split-deriv α₁ α₂ γ (Derivation.⇒*-step {β = β} α⇒β β⇒*γ)
      | inj₂ (β₂ , refl , α₂⇒β₂)
      with split-deriv α₁ β₂ γ β⇒*γ
    ... | γ₁ , γ₂ , eqγ , α₁⇒*γ₁ , β₂⇒*γ₂ =
      γ₁ , γ₂ , eqγ , α₁⇒*γ₁ , Derivation.⇒*-step α₂⇒β₂ β₂⇒*γ₂

    terminal-concat : ∀ u v →
      map inject₁ (Grammar.terminals CFG-instance G₁ u) ++ map inject₂ (Grammar.terminals CFG-instance G₂ v)
      ≡ Grammar.terminals CFG-instance G (u ++ v)
    terminal-concat ε ε = refl
    terminal-concat ε (a ∷ v) = cong (inj₂ a ∷_) (terminal-concat ε v)
    terminal-concat (a ∷ u) v = cong (inj₂ a ∷_) (terminal-concat u v)

    terminal-head : ∀ {a b : Σ} → _≡_ {A = Symbol G} (inj₂ a) (inj₂ b) → a ≡ b
    terminal-head refl = refl

    terminal₂-split : ∀ w β₂ →
      Grammar.terminals CFG-instance G w ≡ map inject₂ β₂ →
      β₂ ≡ Grammar.terminals CFG-instance G₂ w
    terminal₂-split ε ε refl = refl
    terminal₂-split ε (inj₁ A₂ ∷ β₂) ()
    terminal₂-split ε (inj₂ a ∷ β₂) ()
    terminal₂-split (a ∷ w) ε ()
    terminal₂-split (a ∷ w) (inj₁ A₂ ∷ β₂) ()
    terminal₂-split (a ∷ w) (inj₂ b ∷ β₂) eq =
      cong₂ _∷_
        (cong inj₂ (sym (terminal-head (∷-head eq))))
        (terminal₂-split w β₂ (∷-tail eq))

    terminal-split : ∀ w β₁ β₂ →
      Grammar.terminals CFG-instance G w ≡ map inject₁ β₁ ++ map inject₂ β₂ →
      ∃[ u ] ∃[ v ] w ≡ u ++ v
        × β₁ ≡ Grammar.terminals CFG-instance G₁ u
        × β₂ ≡ Grammar.terminals CFG-instance G₂ v
    terminal-split w ε β₂ eq = ε , w , refl , refl , terminal₂-split w β₂ eq
    terminal-split ε (inj₁ A₁ ∷ β₁) β₂ ()
    terminal-split ε (inj₂ a ∷ β₁) β₂ ()
    terminal-split (a ∷ w) (inj₁ A₁ ∷ β₁) β₂ ()
    terminal-split (a ∷ w) (inj₂ b ∷ β₁) β₂ eq
      with terminal-split w β₁ β₂ (∷-tail eq)
    ... | u , v , eqw , eqβ₁ , eqβ₂ =
      a ∷ u , v , cong (a ∷_) eqw
      , cong₂ _∷_ (cong inj₂ (sym (terminal-head (∷-head eq)))) eqβ₁
      , eqβ₂

    start-step-inversion : ∀ β → (Grammar.start CFG-instance G ⇒ β) →
      β ≡ map inject₁ (Grammar.start CFG-instance G₁) ++ map inject₂ (Grammar.start CFG-instance G₂)
    start-step-inversion β (γ₁ , A , δ , γ₂ , eq-in , δ∈PA , eq-out)
      with lemma-eq-++ γ₁ γ₂ eq-in
    ... | refl , refl , refl = trans eq-out (trans (++-identityʳ δ) (sym δ∈PA))

    ⇒*-nonrefl-step : ∀ {α β} → α ≢ β → α ⇒* β → ∃[ γ ] α ⇒ γ × γ ⇒* β
    ⇒*-nonrefl-step neq (Derivation.⇒*-refl α) = ⊥-elim (neq refl)
    ⇒*-nonrefl-step neq (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) = β , α⇒β , β⇒*γ

    correct-left-direct : Lang G ⊆ Lang G₁ · Lang G₂
    correct-left-direct w deriv
      with ⇒*-nonrefl-step (Grammar.start≢terminals CFG-instance G w) deriv
    ... | β , start⇒β , β⇒*w
      rewrite start-step-inversion β start⇒β
      with split-deriv (Grammar.start CFG-instance G₁) (Grammar.start CFG-instance G₂) (Grammar.terminals CFG-instance G w) β⇒*w
    ... | β₁ , β₂ , eqβ , S₁⇒*β₁ , S₂⇒*β₂
      with terminal-split w β₁ β₂ eqβ
    ... | u , v , eqw , refl , refl = u , v , eqw , S₁⇒*β₁ , S₂⇒*β₂

    correct-leftˡ : Leftmost-Derivation.Lang^l G ⊆ Lang G₁ · Lang G₂
    correct-leftˡ w deriv =
      correct-left-direct w (Leftmost-Derivation.Lang^l⊆Lang G w deriv)

    correct-left : Lang G ⊆ Lang G₁ · Lang G₂
    correct-left w deriv =
      correct-leftˡ w (Leftmost-Derivation.Lang⊆Lang^l G w deriv)

    sim₁ : ∀ α₁ β₁ → α₁ ⇒₁ β₁ → map inject₁ α₁ ⇒ map inject₁ β₁
    sim₁ α₁ β₁ (γ₁ , A₁ , δ , γ₂ , refl , δ∈P , refl) =
      map inject₁ γ₁
      , inj₂ (inj₁ A₁)
      , map inject₁ δ
      , map inject₁ γ₂
      , map-++ inject₁ γ₁ (inj₁ A₁ ∷ γ₂)
      , inject-project₁ δ δ∈P
      , trans (map-++ inject₁ γ₁ (δ ++ γ₂))
          (cong (map inject₁ γ₁ ++_) (map-++ inject₁ δ γ₂))
      where
        inject-project₁-map : ∀ δ → U.mapMaybe (map (U.project₁ G₁ G₂) (map inject₁ δ)) ≡ just δ
        inject-project₁-map ε = refl
        inject-project₁-map (inj₁ x ∷ δ) rewrite inject-project₁-map δ = refl
        inject-project₁-map (inj₂ y ∷ δ) rewrite inject-project₁-map δ = refl

        inject-project₁ : ∀ {X : 𝔓 (Word Symbol₁)} δ → δ ∈ X → map inject₁ δ ∈ U.narrow (U.project₁ G₁ G₂) X
        inject-project₁ δ δ∈X rewrite inject-project₁-map δ = δ∈X

    sim₁* : ∀ α₁ β₁ → α₁ ⇒*₁ β₁ → map inject₁ α₁ ⇒* map inject₁ β₁
    sim₁* α₁ β₁ (Derivation.⇒*-refl α) = ⇒*-refl (map inject₁ α₁)
    sim₁* α₁ β₁ (Derivation.⇒*-step {β = β} α₁⇒β β⇒*β₁) =
      ⇒*-step (sim₁ α₁ β α₁⇒β) (sim₁* β β₁ β⇒*β₁)

    sim₂ : ∀ α₂ β₂ → α₂ ⇒₂ β₂ → map inject₂ α₂ ⇒ map inject₂ β₂
    sim₂ α₂ β₂ (γ₁ , A₂ , δ , γ₂ , refl , δ∈P , refl) =
      map inject₂ γ₁
      , inj₂ (inj₂ A₂)
      , map inject₂ δ
      , map inject₂ γ₂
      , map-++ inject₂ γ₁ (inj₁ A₂ ∷ γ₂)
      , inject-project₂ δ δ∈P
      , trans (map-++ inject₂ γ₁ (δ ++ γ₂))
          (cong (map inject₂ γ₁ ++_) (map-++ inject₂ δ γ₂))
      where
        inject-project₂-map : ∀ δ → U.mapMaybe (map (U.project₂ G₁ G₂) (map inject₂ δ)) ≡ just δ
        inject-project₂-map ε = refl
        inject-project₂-map (inj₁ x ∷ δ) rewrite inject-project₂-map δ = refl
        inject-project₂-map (inj₂ y ∷ δ) rewrite inject-project₂-map δ = refl

        inject-project₂ : ∀ {X : 𝔓 (Word Symbol₂)} δ → δ ∈ X → map inject₂ δ ∈ U.narrow (U.project₂ G₁ G₂) X
        inject-project₂ δ δ∈X rewrite inject-project₂-map δ = δ∈X

    sim₂* : ∀ α₂ β₂ → α₂ ⇒*₂ β₂ → map inject₂ α₂ ⇒* map inject₂ β₂
    sim₂* α₂ β₂ (Derivation.⇒*-refl α) = ⇒*-refl (map inject₂ α₂)
    sim₂* α₂ β₂ (Derivation.⇒*-step {β = β} α₂⇒β β⇒*β₂) =
      ⇒*-step (sim₂ α₂ β α₂⇒β) (sim₂* β β₂ β⇒*β₂)

    step-++ʳ : ∀ {α β} γ → α ⇒ β → (α ++ γ) ⇒ (β ++ γ)
    step-++ʳ γ (u , A , y , v , eq-in , y∈PA , eq-out) =
      u , A , y , v ++ γ
      , trans (cong (_++ γ) eq-in) (++-assoc u (inj₁ A ∷ v) γ)
      , y∈PA
      , trans (cong (_++ γ) eq-out)
          (trans (++-assoc u (y ++ v) γ)
            (cong (u ++_) (++-assoc y v γ)))

    step-++ˡ : ∀ α {β γ} → β ⇒ γ → (α ++ β) ⇒ (α ++ γ)
    step-++ˡ α (u , A , y , v , eq-in , y∈PA , eq-out) =
      α ++ u , A , y , v
      , trans (cong (α ++_) eq-in) (sym (++-assoc α u (inj₁ A ∷ v)))
      , y∈PA
      , trans (cong (α ++_) eq-out) (sym (++-assoc α u (y ++ v)))

    ⇒*-trans : ∀ {α β γ} → α ⇒* β → β ⇒* γ → α ⇒* γ
    ⇒*-trans (Derivation.⇒*-refl α) β⇒*γ = β⇒*γ
    ⇒*-trans (Derivation.⇒*-step α⇒β β⇒*γ) γ⇒*δ =
      Derivation.⇒*-step α⇒β (⇒*-trans β⇒*γ γ⇒*δ)

    ⇒*-++ʳ : ∀ {α β} γ → α ⇒* β → (α ++ γ) ⇒* (β ++ γ)
    ⇒*-++ʳ γ (Derivation.⇒*-refl α) = Derivation.⇒*-refl (α ++ γ)
    ⇒*-++ʳ γ (Derivation.⇒*-step α⇒β β⇒*γ) =
      Derivation.⇒*-step (step-++ʳ γ α⇒β) (⇒*-++ʳ γ β⇒*γ)

    ⇒*-++ˡ : ∀ α {β γ} → β ⇒* γ → (α ++ β) ⇒* (α ++ γ)
    ⇒*-++ˡ α (Derivation.⇒*-refl β) = Derivation.⇒*-refl (α ++ β)
    ⇒*-++ˡ α (Derivation.⇒*-step β⇒γ γ⇒*δ) =
      Derivation.⇒*-step (step-++ˡ α β⇒γ) (⇒*-++ˡ α γ⇒*δ)

    correct-right : Lang G₁ · Lang G₂ ⊆ Lang G
    correct-right w (u , v , refl , u∈L₁ , v∈L₂) =
      Derivation.⇒*-step
        (ε , S G
        , map inject₁ (Grammar.start CFG-instance G₁) ++ map inject₂ (Grammar.start CFG-instance G₂)
        , ε , refl , refl , refl)
        (subst
          (λ γ → (map inject₁ (Grammar.start CFG-instance G₁) ++ map inject₂ (Grammar.start CFG-instance G₂)) ⇒* γ)
          (terminal-concat u v)
          (⇒*-trans
            (⇒*-++ʳ (map inject₂ (Grammar.start CFG-instance G₂))
              (sim₁* (Grammar.start CFG-instance G₁) (Grammar.terminals CFG-instance G₁ u) u∈L₁))
            (⇒*-++ˡ (map inject₁ (Grammar.terminals CFG-instance G₁ u))
              (sim₂* (Grammar.start CFG-instance G₂) (Grammar.terminals CFG-instance G₂ v) v∈L₂))))

    correct : Lang G ≐ Lang G₁ · Lang G₂
    correct = correct-left , correct-right

module Kleene {Σ : Set} where

  module U = Union {Σ}

  open CFG using (S; Symbol)
  module _ (G₁ : CFG Σ) where
    open CFG G₁ renaming (N to N₁; S to S₁; P to P₁; Symbol to Symbol₁; _⇒_ to _⇒₁_)

    G₀ : CFG Σ
    G₀ =
      record
      { N = ⊤
      ; S = tt
      ; P = λ _ _ → ⊥
      }

    N₀ = CFG.N G₀

    inject₁ : Symbol₁ → (⊤ ⊎ N₁ ⊎ N₀) ⊎ Σ
    inject₁ (inj₁ x) = inj₁ (inj₂ (inj₁ x))
    inject₁ (inj₂ a) = inj₂ a

    G : CFG Σ
    G =
      record
      { N = ⊤ ⊎ (N₁ ⊎ N₀)
      ; S = inj₁ tt
      ; P = productions
      }
      where
        productions : _
        productions (inj₁ tt) = ｛ ε  ｝
                              ∪ ｛ inj₁ (inj₂ (inj₁ S₁)) ∷ inj₁ (inj₁ tt) ∷ ε ｝
        productions (inj₂ (inj₁ A₁)) = U.narrow (U.project₁ G₁ G₀) (P₁ A₁)
        productions (inj₂ (inj₂ A₀)) δ = ⊥

    open Generated
    open Derivation G
    open Derivation G₁ using () renaming (_⇒*_ to _⇒*₁_)

    sentential₁ : 𝔓 (Word (Symbol G))
    sentential₁ = U.sentential₁ G₁ G₀

    start-sentential₁ : sentential₁ (map inject₁ (Grammar.start CFG-instance G₁))
    start-sentential₁ = tt , tt

    sen-preserve₁ : ∀ α β → sentential₁ α → α ⇒ β → sentential₁ β
    sen-preserve₁ α β senα (γ₁ , A , δ , γ₂ , refl , δ∈P , refl)
      with U.sentential₁-++ G₁ G₀ γ₁ _ senα
    sen-preserve₁ .(γ₁ ++ inj₁ (inj₁ tt) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₁ tt , δ , γ₂ , refl , δ∈P , refl) | senγ₁ , ()
    sen-preserve₁ .(γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , refl , δ∈P , refl) | senγ₁ , tt , senγ₂
      using senδ ← U.project-sentential G₁ G₀ δ A₁ δ∈P
      = U.sentential₁-++⁺ G₁ G₀ γ₁ (δ ++ γ₂) senγ₁ (U.sentential₁-++⁺ G₁ G₀ δ γ₂ senδ senγ₂)
    sen-preserve₁* : ∀ α β → sentential₁ α → α ⇒* β → sentential₁ β
    sen-preserve₁* α β senα (Derivation.⇒*-refl α) = senα
    sen-preserve₁* α γ senα (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) =
      sen-preserve₁* β γ (sen-preserve₁ α β senα α⇒β) β⇒*γ

    sim₁- : ∀ α β → (senα : sentential₁ α) → (step : α ⇒ β) →
      U.project-sen₁ G₁ G₀ α senα ⇒₁ U.project-sen₁ G₁ G₀ β (sen-preserve₁ α β senα step)
    sim₁- .(γ₁ ++ inj₁ (inj₁ tt) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₁ tt , δ , γ₂ , refl , δ∈P , refl)
      with U.sentential₁-++ G₁ G₀ γ₁ (inj₁ (inj₁ tt) ∷ γ₂) senα
    ... | senγ₁ , ()
    sim₁- .(γ₁ ++ inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₁ A₁) , δ , γ₂ , refl , δ∈P , refl)
      = U.project-sen₁ G₁ G₀ γ₁ senγ₁
      , A₁
      , U.project-sen₁ G₁ G₀ δ senδ
      , U.project-sen₁ G₁ G₀ γ₂ senγ₂
      , U.project-sen₁-++ G₁ G₀ γ₁ (inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) senα
      , U.project-production₁ G₁ G₀ δ A₁ δ∈P senδ
      , trans (U.project-sen₁-++⁺ G₁ G₀ γ₁ (δ ++ γ₂) senγ₁ (U.sentential₁-++⁺ G₁ G₀ δ γ₂ senδ senγ₂))
          (cong (U.project-sen₁ G₁ G₀ γ₁ senγ₁ ++_) (U.project-sen₁-++⁺ G₁ G₀ δ γ₂ senδ senγ₂))
      where
        split = U.sentential₁-++ G₁ G₀ γ₁ (inj₁ (inj₂ (inj₁ A₁)) ∷ γ₂) senα
        senγ₁ = split .proj₁
        senγ₂ = split .proj₂ .proj₂
        senδ = U.project-sentential G₁ G₀ δ A₁ δ∈P
    sim₁- .(γ₁ ++ inj₁ (inj₂ (inj₂ A₀)) ∷ γ₂) .(γ₁ ++ δ ++ γ₂) senα (γ₁ , inj₂ (inj₂ A₀) , δ , γ₂ , refl , () , refl)

    sim₁*- : ∀ α β → (senα : sentential₁ α) → (d : α ⇒* β) →
      U.project-sen₁ G₁ G₀ α senα ⇒*₁ U.project-sen₁ G₁ G₀ β (sen-preserve₁* α β senα d)
    sim₁*- α β senα (Derivation.⇒*-refl α) = Derivation.⇒*-refl (U.project-sen₁ G₁ G₀ α senα)
    sim₁*- α γ senα (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) =
      Derivation.⇒*-step (sim₁- α β senα α⇒β) (sim₁*- β γ (sen-preserve₁ α β senα α⇒β) β⇒*γ)

    inject-project₁-map : ∀ δ → U.mapMaybe (map (U.project₁ G₁ G₀) (map inject₁ δ)) ≡ just δ
    inject-project₁-map ε = refl
    inject-project₁-map (inj₁ x ∷ δ) rewrite inject-project₁-map δ = refl
    inject-project₁-map (inj₂ y ∷ δ) rewrite inject-project₁-map δ = refl

    inject-project₁ : ∀ {X : 𝔓 (Word Symbol₁)} δ → δ ∈ X → map inject₁ δ ∈ U.narrow (U.project₁ G₁ G₀) X
    inject-project₁ δ δ∈X rewrite inject-project₁-map δ = δ∈X

    sim₁ : ∀ α₁ β₁ → α₁ ⇒₁ β₁ → map inject₁ α₁ ⇒ map inject₁ β₁
    sim₁ α₁ β₁ (γ₁ , A₁ , δ , γ₂ , refl , δ∈P , refl) =
      map inject₁ γ₁
      , inj₂ (inj₁ A₁)
      , map inject₁ δ
      , map inject₁ γ₂
      , map-++ inject₁ γ₁ (inj₁ A₁ ∷ γ₂)
      , inject-project₁ δ δ∈P
      , trans (map-++ inject₁ γ₁ (δ ++ γ₂))
          (cong (map inject₁ γ₁ ++_) (map-++ inject₁ δ γ₂))

    sim₁* : ∀ α₁ β₁ → α₁ ⇒*₁ β₁ → map inject₁ α₁ ⇒* map inject₁ β₁
    sim₁* α₁ β₁ (Derivation.⇒*-refl α) = ⇒*-refl (map inject₁ α₁)
    sim₁* α₁ β₁ (Derivation.⇒*-step {β = β} α₁⇒β β⇒*β₁) =
      ⇒*-step (sim₁ α₁ β α₁⇒β) (sim₁* β β₁ β⇒*β₁)

    step-++ʳ : ∀ {α β} γ → α ⇒ β → (α ++ γ) ⇒ (β ++ γ)
    step-++ʳ γ (u , A , y , v , eq-in , y∈PA , eq-out) =
      u , A , y , v ++ γ
      , trans (cong (_++ γ) eq-in) (++-assoc u (inj₁ A ∷ v) γ)
      , y∈PA
      , trans (cong (_++ γ) eq-out)
          (trans (++-assoc u (y ++ v) γ)
            (cong (u ++_) (++-assoc y v γ)))

    step-++ˡ : ∀ α {β γ} → β ⇒ γ → (α ++ β) ⇒ (α ++ γ)
    step-++ˡ α (u , A , y , v , eq-in , y∈PA , eq-out) =
      α ++ u , A , y , v
      , trans (cong (α ++_) eq-in) (sym (++-assoc α u (inj₁ A ∷ v)))
      , y∈PA
      , trans (cong (α ++_) eq-out) (sym (++-assoc α u (y ++ v)))

    ⇒*-trans : ∀ {α β γ} → α ⇒* β → β ⇒* γ → α ⇒* γ
    ⇒*-trans (Derivation.⇒*-refl α) β⇒*γ = β⇒*γ
    ⇒*-trans (Derivation.⇒*-step α⇒β β⇒*γ) γ⇒*δ =
      Derivation.⇒*-step α⇒β (⇒*-trans β⇒*γ γ⇒*δ)

    ⇒*-++ʳ : ∀ {α β} γ → α ⇒* β → (α ++ γ) ⇒* (β ++ γ)
    ⇒*-++ʳ γ (Derivation.⇒*-refl α) = Derivation.⇒*-refl (α ++ γ)
    ⇒*-++ʳ γ (Derivation.⇒*-step α⇒β β⇒*γ) =
      Derivation.⇒*-step (step-++ʳ γ α⇒β) (⇒*-++ʳ γ β⇒*γ)

    ⇒*-++ˡ : ∀ α {β γ} → β ⇒* γ → (α ++ β) ⇒* (α ++ γ)
    ⇒*-++ˡ α (Derivation.⇒*-refl β) = Derivation.⇒*-refl (α ++ β)
    ⇒*-++ˡ α (Derivation.⇒*-step β⇒γ γ⇒*δ) =
      Derivation.⇒*-step (step-++ˡ α β⇒γ) (⇒*-++ˡ α γ⇒*δ)

    terminal-concat : ∀ u v →
      map inject₁ (Grammar.terminals CFG-instance G₁ u) ++ Grammar.terminals CFG-instance G v
      ≡ Grammar.terminals CFG-instance G (u ++ v)
    terminal-concat ε v = refl
    terminal-concat (a ∷ u) v = cong (inj₂ a ∷_) (terminal-concat u v)

    start-empty : Grammar.start CFG-instance G ⇒ ε
    start-empty = ε , S G , ε , ε , refl , inj₁ refl , refl

    start-cons :
      Grammar.start CFG-instance G ⇒
      map inject₁ (Grammar.start CFG-instance G₁) ++ Grammar.start CFG-instance G
    start-cons =
      ε , S G
      , inj₁ (inj₂ (inj₁ S₁)) ∷ inj₁ (inj₁ tt) ∷ ε
      , ε
      , refl
      , inj₂ refl
      , refl

    private
      lemma-eq-++ : ∀ {x y : Symbol G} xs ys → [ x ] ≡ xs ++ y ∷ ys → xs ≡ ε × x ≡ y × ys ≡ ε
      lemma-eq-++ ε ys refl = refl , refl , refl
      lemma-eq-++ (x ∷ ε) ys ()
      lemma-eq-++ (x ∷ x₁ ∷ xs) ys ()

    start-step-inversion : ∀ β → Grammar.start CFG-instance G ⇒ β →
        (β ≡ ε)
      ⊎ (β ≡ map inject₁ (Grammar.start CFG-instance G₁) ++ Grammar.start CFG-instance G)
    start-step-inversion β (γ₁ , A , δ , γ₂ , eq-in , δ∈PA , eq-out)
      with lemma-eq-++ γ₁ γ₂ eq-in
    ... | refl , refl , refl with δ∈PA | eq-out
    ... | inj₁ refl | refl = inj₁ refl
    ... | inj₂ refl | refl = inj₂ refl

    ⇒*-nonrefl-step : ∀ {α β} → α ≢ β → α ⇒* β → ∃[ γ ] α ⇒ γ × γ ⇒* β
    ⇒*-nonrefl-step neq (Derivation.⇒*-refl α) = ⊥-elim (neq refl)
    ⇒*-nonrefl-step neq (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) = β , α⇒β , β⇒*γ

    record NonreflStep {α β : Word (Symbol G)} (deriv : α ⇒* β) : Set where
      constructor nonrefl-step
      field
        γ : Word (Symbol G)
        first : α ⇒ γ
        rest : γ ⇒* β
        length-rest : Leftmost-Derivation.⇒*-length G deriv ≡ suc (Leftmost-Derivation.⇒*-length G rest)

    ⇒*-nonrefl-step-length : ∀ {α β} → α ≢ β → (deriv : α ⇒* β) → NonreflStep deriv
    ⇒*-nonrefl-step-length neq (Derivation.⇒*-refl α) = ⊥-elim (neq refl)
    ⇒*-nonrefl-step-length neq (Derivation.⇒*-step {β = β} α⇒β β⇒*γ) =
      nonrefl-step β α⇒β β⇒*γ refl

    terminals-empty : ∀ w → Grammar.terminals CFG-instance G w ≡ ε → 𝟙 w
    terminals-empty ε refl = tt
    terminals-empty (a ∷ w) ()

    project-left : ∀ u →
      map inject₁ (Grammar.start CFG-instance G₁) ⇒* Grammar.terminals CFG-instance G u →
      Lang G₁ u
    project-left u deriv =
      subst
        (λ γ → Grammar.start CFG-instance G₁ ⇒*₁ γ)
        (U.project-sen₁-terminals G₁ G₀ u (sen-preserve₁* _ _ start-sentential₁ deriv))
        (sim₁*- _ _ start-sentential₁ deriv)

    suffix-length< : ∀ i (u v w : Word Σ) → w ≡ u ++ v → length w < i → length v < i
    suffix-length< i u v .(u ++ v) refl lenw<i =
      ≤-<-trans
        (≤-trans (m≤n+m (length v) (length u)) (≤-reflexive (sym (length-++ u {ys = v}))))
        lenw<i

    right-deriv-length< : ∀ j {α₁ α₂ β β₁ β₂ : Word (Symbol G)}
      (deriv : (α₁ ++ α₂) ⇒* β)
      (left : α₁ ⇒* β₁)
      (right : α₂ ⇒* β₂)
      → Leftmost-Derivation.⇒*-length G deriv ≡ Leftmost-Derivation.⇒*-length G left + Leftmost-Derivation.⇒*-length G right
      → Leftmost-Derivation.⇒*-length G deriv < j
      → Leftmost-Derivation.⇒*-length G right < j
    right-deriv-length< j deriv left right len-eq deriv<j =
      ≤-<-trans
        (subst
          (λ n → Leftmost-Derivation.⇒*-length G right ≤ n)
          (sym len-eq)
          (m≤n+m (Leftmost-Derivation.⇒*-length G right) (Leftmost-Derivation.⇒*-length G left)))
        deriv<j

    correct-left-ordinary-gen : ∀ i j w →
      length w < i →
      (deriv : Lang G w) →
      Leftmost-Derivation.⇒*-length G deriv < j →
      (Lang G₁ ∗) w
    correct-left-ordinary-gen zero j w () deriv deriv<j
    correct-left-ordinary-gen i zero w lenw<i deriv ()
    correct-left-ordinary-gen (suc i) (suc j) w lenw<i deriv deriv<j
      with ⇒*-nonrefl-step-length (Grammar.start≢terminals CFG-instance G w) deriv
    ... | nonrefl-step β start⇒β β⇒*w len-rest
      with subst (λ n → n < suc j) len-rest deriv<j
    ... | s≤s β⇒*w<j
      with start-step-inversion β start⇒β
    ... | inj₁ refl =
      zero , terminals-empty w (Leftmost-Derivation.empty-deriv G (Grammar.terminals CFG-instance G w) β⇒*w)
    ... | inj₂ refl
      with Leftmost-Derivation.split-deriv-length G
        (map inject₁ (Grammar.start CFG-instance G₁))
        (Grammar.start CFG-instance G)
        (Grammar.terminals CFG-instance G w)
        β⇒*w
    ... | Leftmost-Derivation.split-length β₁ β₂ eqβ S₁⇒*β₁ S⇒*β₂ len-split
      with Leftmost-Derivation.terminal-split G w β₁ β₂ eqβ
    ... | u , v , eqw , refl , refl
      with correct-left-ordinary-gen
        (suc i)
        j
        v
        (suffix-length< (suc i) u v w eqw lenw<i)
        S⇒*β₂
        (right-deriv-length< j β⇒*w S₁⇒*β₁ S⇒*β₂ len-split β⇒*w<j)
    ... | n , v∈Ln = suc n , u , v , eqw , project-left u S₁⇒*β₁ , v∈Ln

    correct-left-ordinary : Lang G ⊆ (Lang G₁ ∗)
    correct-left-ordinary w deriv =
      correct-left-ordinary-gen
        (suc (length w))
        (suc (Leftmost-Derivation.⇒*-length G deriv))
        w
        ≤-refl
        deriv
        ≤-refl

    correct-right : (Lang G₁ ∗) ⊆ Lang G
    correct-right ε (zero , tt) =
      Derivation.⇒*-step start-empty (Derivation.⇒*-refl ε)
    correct-right (a ∷ w) (zero , ())
    correct-right w (suc n , u , v , eqw , u∈L , v∈Ln) =
      subst (Lang G) (sym eqw)
        (Derivation.⇒*-step start-cons
          (subst
            (λ γ → (map inject₁ (Grammar.start CFG-instance G₁) ++ Grammar.start CFG-instance G) ⇒* γ)
            (terminal-concat u v)
            (⇒*-trans
              (⇒*-++ʳ (Grammar.start CFG-instance G)
                (sim₁* (Grammar.start CFG-instance G₁) (Grammar.terminals CFG-instance G₁ u) u∈L))
              (⇒*-++ˡ (map inject₁ (Grammar.terminals CFG-instance G₁ u))
                (correct-right v (n , v∈Ln))))))

    correct-leftˡ : Leftmost-Derivation.Lang^l G ⊆ (Lang G₁ ∗)
    correct-leftˡ w deriv =
      correct-left-ordinary-gen
        (suc (length w))
        (suc (Leftmost-Derivation.⇒ˡ*-length G deriv))
        w
        ≤-refl
        (Leftmost-Derivation.⇒ˡ*⇒* G deriv)
        (subst
          (λ n → n < suc (Leftmost-Derivation.⇒ˡ*-length G deriv))
          (sym (Leftmost-Derivation.⇒ˡ*⇒*-length G deriv))
          ≤-refl)

    correct-left : Lang G ⊆ (Lang G₁ ∗)
    correct-left = correct-left-ordinary

    correct : Lang G ≐ (Lang G₁ ∗)
    correct = correct-left , correct-right
