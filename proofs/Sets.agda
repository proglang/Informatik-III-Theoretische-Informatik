module Sets where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Empty as Empty hiding (⊥)
open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-monoˡ-≤)
open import Data.Fin using (Fin; zero; suc; remQuot; quotRem; combine; finToFun; funToFin; inject≤; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Subset using (Subset; ⊥; ⊤; Side; inside; outside) renaming (_∈_ to _∈′_)
open import Data.Fin.Properties using (funToFin-finToFin; finToFun-funToFin; combine-remQuot; remQuot-combine; splitAt-join; join-splitAt)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Data.Product using (∃-syntax; _×_; _,_; Σ; proj₁; proj₂)
open import Data.Product.Properties using (×-≡,≡←≡)
open import Data.Sum using (_⊎_; inj₁; inj₂; map; [_,_])
open import Data.Sum.Properties using (map-map; [,]-map; [,]-∘; [,]-cong)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; trans)
open import Relation.Unary using (Pred; _∈_; Decidable)
open import Function using (_∘_)
open import FunExt
open import Isomorphism using (Iso; comp; inverse-iso)
open import Finiteness using (Finite)

-- powerset

𝔓 : ∀{ℓ} → Set ℓ → Set (lsuc ℓ)
𝔓 Q = Pred Q _

non-empty : ∀ {ℓ} {Q : Set ℓ} → 𝔓{ℓ} Q → Set _
non-empty R = ∃[ q ] q ∈ R

infix 5 _≠∅
_≠∅ = non-empty

-- set comprehension notation

｛｝ : ∀ {ℓ}{A : Set ℓ} → A → A
｛｝ = λ z → z

syntax ｛｝ (λ x → M) = ｛ x ∣ M ｝

-- lift function to a set

lift : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}
  → (f : A → Pred B ℓ₁) → (Pred A ℓ₁ → Pred B ℓ₁)
lift f Pa = ｛ b ∣ ∃[ a ] a ∈ Pa × b ∈ f a ｝

lift₂ : ∀ {ℓ}{ℓc} {A : Set ℓ} {C : Set ℓc} {B : Set ℓ}
  → (f : A → B → Pred C ℓ) → (Pred A ℓ → B → Pred C ℓ)
lift₂ f Pa b = ｛ c ∣ ∃[ a ] a ∈ Pa × c ∈ f a b ｝

-- ∀-distrib-×

∀-distrib-× : ∀ {a b} {A : Set a}{P Q : A → Set b} → (∀ x → P x × Q x) → (∀ x → P x) × (∀ x → Q x)
∀-distrib-× ∀PQ = (λ x → ∀PQ x .proj₁) , (λ x → ∀PQ x .proj₂)

-- properties

side→fin : Side → Fin 2
side→fin outside = zero
side→fin inside = suc zero

fin→side : Fin 2 → Side
fin→side zero = outside
fin→side (suc zero) = inside

fin→side∘side→fin : ∀ s → fin→side (side→fin s) ≡ s
fin→side∘side→fin outside = refl
fin→side∘side→fin inside = refl

side→fin∘fin→side : ∀ r → side→fin (fin→side r) ≡ r
side→fin∘fin→side zero = refl
side→fin∘fin→side (suc zero) = refl

subset→fun : ∀ {n} → Subset n → Fin n → Fin 2
subset→fun [] ()
subset→fun (s ∷ xs) zero = side→fin s
subset→fun (s ∷ xs) (suc i) = subset→fun xs i

fun→subset : ∀ {n} → (Fin n → Fin 2) → Subset n
fun→subset {zero} f = []
fun→subset {suc n} f = fin→side (f zero) ∷ fun→subset (λ i → f (suc i))

subset-encode : ∀ {n} → Fin (2 ^ n) → Subset n
subset-encode {n} i = fun→subset (finToFun {m = 2} {n = n} i)

subset-decode : ∀ {n} → Subset n → Fin (2 ^ n)
subset-decode {n} xs = funToFin {m = n} {n = 2} (subset→fun xs)

fun→subset∘subset→fun : ∀ {n} (xs : Subset n) → fun→subset (subset→fun xs) ≡ xs
fun→subset∘subset→fun [] = refl
fun→subset∘subset→fun (s ∷ xs)
  rewrite fin→side∘side→fin s
        | fun→subset∘subset→fun xs
  = refl

subset→fun∘fun→subset : ∀ {n} (f : Fin n → Fin 2) → ∀ i → subset→fun (fun→subset f) i ≡ f i
subset→fun∘fun→subset {zero} f ()
subset→fun∘fun→subset {suc n} f zero = side→fin∘fin→side (f zero)
subset→fun∘fun→subset {suc n} f (suc i) = subset→fun∘fun→subset (λ j → f (suc j)) i

fun→subset-ext : ∀ {n} {f g : Fin n → Fin 2} →
  (∀ i → f i ≡ g i) → fun→subset f ≡ fun→subset g
fun→subset-ext {zero} p = refl
fun→subset-ext {suc n} p
  rewrite cong fin→side (p zero)
        | fun→subset-ext (λ i → p (suc i))
  = refl

funToFin-cong : ∀ {m n} {f g : Fin m → Fin n} →
  (∀ i → f i ≡ g i) → funToFin f ≡ funToFin g
funToFin-cong {zero} p = refl
funToFin-cong {suc m} p
  rewrite p zero
        | funToFin-cong (λ i → p (suc i))
  = refl

subset-iso : ∀ n → Iso (Fin (2 ^ n)) (Subset n)
subset-iso n =
  record {
    fwd = subset-encode
  ; bwd = subset-decode
  ; fwd∘bwd = λ xs →
      trans
        (fun→subset-ext (finToFun-funToFin {m = n} {n = 2} (subset→fun xs)))
        (fun→subset∘subset→fun xs)
  ; bwd∘fwd = λ i →
      trans
        (funToFin-cong (subset→fun∘fun→subset (finToFun {m = 2} {n = n} i)))
        (funToFin-finToFin {m = n} {n = 2} i)
  }

postulate
  power-iso : ∀ {ℓ} {X : Set ℓ} n → Iso X (Fin n) → Iso (𝔓 X) (Subset n)

Finite-𝔓 : ∀ {ℓ} {X : Set ℓ} → Finite X → Finite (𝔓 X)
Finite-𝔓 (n , iso)
  = (2 ^ n)
  , comp (power-iso n iso) (inverse-iso (subset-iso n))
