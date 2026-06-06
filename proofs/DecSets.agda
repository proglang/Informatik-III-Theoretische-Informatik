module DecSets where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; T)
open import Data.Nat using (ℕ; zero; suc; _^_)
open import Data.Fin using (Fin; zero; suc; finToFun; funToFin)
open import Data.Fin.Subset using (Subset; Side; inside; outside) renaming (_∈_ to _∈′_)
open import Data.Fin.Properties using (funToFin-finToFin; finToFun-funToFin)
open import Data.Vec using (Vec; []; _∷_; tabulate; lookup)
open import Data.Vec.Properties using (tabulate∘lookup; lookup∘tabulate)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Isomorphism using (Iso; comp; inverse-iso)

open import FunExt
open import Finiteness

𝔓 : ∀ {ℓ} → Set ℓ → Set ℓ
𝔓 X = X → Bool

infix 4 _∈_ _∈ᵇ_

_∈ᵇ_ : ∀ {ℓ} {X : Set ℓ} → X → 𝔓 X → Bool
x ∈ᵇ R = R x

_∈_ : ∀ {ℓ} {X : Set ℓ} → X → 𝔓 X → Set
x ∈ R = T (x ∈ᵇ R)

infix 5 _≠∅

non-empty : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → Set ℓ
non-empty R = ∃[ x ] x ∈ R

_≠∅ = non-empty

infixr 7 _∩_
infixr 6 _∪_
infix 4 _⊆_ _≐_

U : ∀ {ℓ} {X : Set ℓ} → 𝔓 X
U _ = true

∅ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X
∅ _ = false

_∩_ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → 𝔓 X → 𝔓 X
(R ∩ S) x = R x ∧ S x

_∪_ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → 𝔓 X → 𝔓 X
(R ∪ S) x = R x ∨ S x

∁ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → 𝔓 X
∁ R x = not (R x)

_⊆_ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → 𝔓 X → Set ℓ
R ⊆ S = ∀ x → x ∈ R → x ∈ S

_≐_ : ∀ {ℓ} {X : Set ℓ} → 𝔓 X → 𝔓 X → Set ℓ
R ≐ S = (R ⊆ S) × (S ⊆ R)

-- set comprehension notation
｛｝ : ∀ {ℓ} {A : Set ℓ} → A → A
｛｝ = λ z → z

syntax ｛｝ (λ x → M) = ｛ x ∣ M ｝

-- finite subsets as vectors of booleans

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

power-iso : ∀ {ℓ} {X : Set ℓ} n → Iso X (Fin n) → Iso (𝔓 X) (Subset n)
power-iso {X = X} n iso-xf =
  record
    { fwd = λ P → tabulate (λ i → iso-xf .Iso.bwd i ∈ᵇ P)
    ; bwd = λ ss x → lookup ss (iso-xf .Iso.fwd x)
    ; fwd∘bwd = λ ss →
        trans
          (cong tabulate (funext (λ i → cong (lookup ss) (iso-xf .Iso.fwd∘bwd i))))
          (tabulate∘lookup ss)
    ; bwd∘fwd = λ P →
        funext (λ x →
          trans
            (lookup∘tabulate (λ i → iso-xf .Iso.bwd i ∈ᵇ P) (iso-xf .Iso.fwd x))
            (cong (λ z → z ∈ᵇ P) (iso-xf .Iso.bwd∘fwd x)))
    }

Finite-𝔓 : ∀ {ℓ} {X : Set ℓ} → Finite X → Finite (𝔓 X)
Finite-𝔓 (n , iso)
  = (2 ^ n)
  , comp (power-iso n iso) (inverse-iso (subset-iso n))
