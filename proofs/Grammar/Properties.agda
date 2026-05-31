module Grammar.Properties where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; _++_; map; length; [_]) renaming (List to Word; [] to ε)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (∃-syntax; _×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; dcong₂)
open import Relation.Unary using (_∈_)

open import FunExt
open import Sets using (𝔓; ｛｝)
open import Language using (Language)

open import Grammar

open import Isomorphism

module CFG-iso {Ω : Set} where
  open Grammar.Grammar
  
  cfg-iso : Iso (Σ (Grammar Ω) CFG-property) (CFG Ω)
  cfg-iso = record
    { fwd = fwd-map
    ; bwd = bwd-map
    ; fwd∘bwd = fwd∘bwd-map
    ; bwd∘fwd = bwd∘fwd-map
    }
    where
      fwd-map : _
      fwd-map (G , is-CFG) =
        record
          { N = N G
          ; S = S G
          ; P = λ A → ｛ β ∣ ([ inj₁ A ] , β) ∈ (P G) ｝
          }
      bwd-map : _
      bwd-map G =
        record
          { N = CFG.N G
          ; S = CFG.S G
          ; P = ｛ (α , β) ∣ (∃[ A ] α ≡ [ inj₁ A ] × β ∈ CFG.P G A) ｝
          ; P-lhs-condition = λ{ (A , refl , snd) → tt}
          }
        , λ{ (A , refl , snd) → refl}
      fwd∘bwd-map : _
      fwd∘bwd-map record { N = N₁ ; S = S₁ ; P = P₁ }
        = {!!}
      bwd∘fwd-map : _
      bwd∘fwd-map (record { N = N₁ ; S = S₁ ; P = P₁ ; P-lhs-condition = P-lhs-condition₁ }
                  , cfg-prop)
        = {!!}
