module Finiteness where

open import Level using (Level)
open import Data.Nat using (ℕ; _^_; _*_; _+_)
open import Data.Fin using (Fin; remQuot; quotRem; combine; finToFun; funToFin; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties using (funToFin-finToFin; finToFun-funToFin; combine-remQuot; remQuot-combine; splitAt-join; join-splitAt)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (×-≡,≡←≡)
open import Data.Sum using (_⊎_; inj₁; inj₂; map; [_,_])
open import Data.Sum.Properties using (map-map; [,]-map; [,]-cong)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans)
open import Function using (_∘_)
open import FunExt
open import Isomorphism using (Iso)

variable
  ℓ ℓ₁ ℓ₂ : Level

Finite : ∀ {ℓ} → Set ℓ → Set ℓ
Finite X = ∃[ n ] Iso X (Fin n)

Finite-× : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} → Finite X → Finite Y → Finite (X × Y)
Finite-× (nx , isox) (ny , isoy)
  = (nx * ny)
  , (record
    { fwd = λ{ (x , y) → combine (fwd₁ x) (fwd₂ y)}
    ; bwd = λ x → let (fx , fy) =  remQuot ny x in bwd₁ fx , bwd₂ fy
    ; fwd∘bwd = fwd∘bwd-map
    ; bwd∘fwd = bwd∘fwd-map
    })
  where
    open Iso isox renaming (fwd to fwd₁; bwd to bwd₁; fwd∘bwd to fwd∘bwd₁ ; bwd∘fwd to bwd∘fwd₁)
    open Iso isoy renaming (fwd to fwd₂; bwd to bwd₂; fwd∘bwd to fwd∘bwd₂ ; bwd∘fwd to bwd∘fwd₂)
    fwd∘bwd-map : _
    fwd∘bwd-map b = trans (cong₂ combine (fwd∘bwd₁ (quotRem ny b .proj₂)) (fwd∘bwd₂ (quotRem{m = nx} ny b .proj₁))) (combine-remQuot {n = nx} ny b)
    bwd∘fwd-map : _
    bwd∘fwd-map (x , y)
      with remQuot-combine (fwd₁ x) (fwd₂ y)
    ... | eq²
      with ×-≡,≡←≡  eq²
    ... | eqx , eqy
      rewrite eqx | eqy = cong₂ _,_ (bwd∘fwd₁ x) (bwd∘fwd₂ y)

Finite-⊎ : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} → Finite X → Finite Y → Finite (X ⊎ Y)
Finite-⊎ (nx , isox) (ny , isoy)
  = (nx + ny)
  , (record
    { fwd = λ x → join nx ny (map fwd₁ fwd₂ x)
    ; bwd = λ x → map bwd₁ bwd₂ (splitAt nx x)
    ; fwd∘bwd = fwd∘bwd-map
    ; bwd∘fwd = bwd∘fwd-map
    })
  where
    open Iso isox renaming (fwd to fwd₁; bwd to bwd₁; fwd∘bwd to fwd∘bwd₁ ; bwd∘fwd to bwd∘fwd₁)
    open Iso isoy renaming (fwd to fwd₂; bwd to bwd₂; fwd∘bwd to fwd∘bwd₂ ; bwd∘fwd to bwd∘fwd₂)

    fwd∘bwd-map : _
    fwd∘bwd-map b
      rewrite map-map  {f = bwd₁} {g = bwd₂} {fwd₁} {fwd₂} (splitAt nx b)
        = trans ([,]-map (splitAt nx b))
          (trans ([,]-cong (λ x → cong (_↑ˡ ny) (fwd∘bwd₁ x))
                           (λ y → cong (nx ↑ʳ_) (fwd∘bwd₂ y))
                           (splitAt nx b))
                 (join-splitAt nx ny b))

    bwd∘fwd-map : _
    bwd∘fwd-map (inj₁ x)
      rewrite splitAt-join nx ny (map fwd₁ fwd₂ (inj₁ x)) = cong inj₁ (bwd∘fwd₁ x)
    bwd∘fwd-map (inj₂ y)
      rewrite splitAt-join nx ny (map fwd₁ fwd₂ (inj₂ y)) = cong inj₂ (bwd∘fwd₂ y)

Finite-⇒ : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} → Finite X → Finite Y → Finite (X → Y)
Finite-⇒ {X = X}{Y} (nx , isox) (ny , isoy)
  = ny ^ nx
  , record
    { fwd = λ f → funToFin (fwd₂ ∘ f ∘ bwd₁)
    ; bwd = λ fxy → bwd₂ ∘ finToFun fxy ∘ fwd₁
    ; fwd∘bwd = fwd∘bwd-helper
    ; bwd∘fwd = λ a → funext (bwd∘fwd-helper a)
    }
  where
    open Iso isox renaming (fwd to fwd₁; bwd to bwd₁; fwd∘bwd to fwd∘bwd₁ ; bwd∘fwd to bwd∘fwd₁)
    open Iso isoy renaming (fwd to fwd₂; bwd to bwd₂; fwd∘bwd to fwd∘bwd₂ ; bwd∘fwd to bwd∘fwd₂)

    bwd∘fwd-helper : ∀ (a : X → Y) x →
      bwd₂ (finToFun (funToFin (λ x₁ → fwd₂ (a (bwd₁ x₁)))) (fwd₁ x)) ≡ a x
    bwd∘fwd-helper a x
      rewrite finToFun-funToFin (λ x₁ → fwd₂ (a (bwd₁ x₁))) (fwd₁ x)
        = trans (bwd∘fwd₂ (a (bwd₁ (fwd₁ x)))) (cong a (bwd∘fwd₁ x))

    fwd∘bwd-helper : ∀ b → funToFin (λ x → fwd₂ (bwd₂ (finToFun b (fwd₁ (bwd₁ x))))) ≡ b
    fwd∘bwd-helper b = trans (cong funToFin (funext (λ x → fwd∘bwd₂ (finToFun b (fwd₁ (bwd₁ x))))))
                      (trans (cong funToFin (funext (λ z → cong (finToFun b) (fwd∘bwd₁ z))))
                             (funToFin-finToFin {m = nx}{n = ny} b))
