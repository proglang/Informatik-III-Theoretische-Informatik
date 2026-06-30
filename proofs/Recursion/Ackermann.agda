module Recursion.Ackermann where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; zero; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-comm; n<1+n; m≤n⇒∃[o]m+o≡n;
  <-trans; <⇒≤; <-≤-trans; ≤-<-trans; ≤-refl; ≤-trans)
open import Data.Product using (∃; _,_; proj₁; proj₂)

-- the ackermann function

A : ℕ → ℕ → ℕ
A zero y = suc y
A (suc x) zero = A x 1
A (suc x) (suc y) = A x (A (suc x) y)

-- monotonicity properties

A>0 : ∀ x y → 0 < A x y
A>0 zero    y        = s≤s z≤n
A>0 (suc x) zero     = A>0 x 1
A>0 (suc x) (suc y)  = A>0 x (A (suc x) y)

-- Property (1)
A-incr-y : ∀ x y → y < A x y
A-incr-y zero    y        = n<1+n y
A-incr-y (suc x) zero     = A>0 x 1
A-incr-y (suc x) (suc y)  = ≤-<-trans (A-incr-y (suc x) y)
                                     (A-incr-y x (A (suc x) y))

A-incr-y1 : ∀ y → suc y < A 1 y
A-incr-y1 zero = s≤s (s≤s z≤n)
A-incr-y1 (suc y) = s≤s (A-incr-y1 y)

-- Property (2)
A-mono-y1 : ∀ x y → A x y < A x (suc y)
A-mono-y1 zero y = n<1+n (suc y)
A-mono-y1 (suc x) y = A-incr-y x (A (suc x) y)

A-mono-yk : ∀ x y k → A x y < A x (suc k + y)
A-mono-yk x y zero = A-mono-y1 x y
A-mono-yk x y (suc k) = <-trans (A-mono-yk x y k) (A-mono-y1 x (suc k + y))

A-mono-y : ∀ x y₁ y₂ → y₁ < y₂ → A x y₁ < A x y₂
A-mono-y x y₁ y₂ y₁<y₂
  with m≤n⇒∃[o]m+o≡n y₁<y₂
... | k , refl
  rewrite +-comm y₁ k = A-mono-yk x y₁ k

-- maybe shorten this using m≤n⇒m<n∨m≡n?
A-mono-y≤ : ∀ x y₁ y₂ → y₁ ≤ y₂ → A x y₁ ≤ A x y₂
A-mono-y≤ x y₁ y₂ y₁≤y₂
  with m≤n⇒∃[o]m+o≡n y₁≤y₂
... | zero , refl rewrite +-identityʳ y₁ = ≤-refl
... | suc k , refl rewrite +-comm y₁ (suc k) = <⇒≤ (A-mono-yk x y₁ k)

-- Property (3)
A-move-xy : ∀ x y → A x (suc y) ≤ A (suc x) y
A-move-xy x zero = ≤-refl
A-move-xy x (suc y) = ≤-trans (A-mono-y≤ x (suc (suc y)) (A x (suc y)) (A-incr-y x (suc y)))
                              (A-mono-y≤ x (A x (suc y)) (A (suc x) y) (A-move-xy x y))

-- Property (4)
A-mono-x : ∀ x y → A x y < A (suc x) y
A-mono-x x y = <-≤-trans (A-mono-y1 x y) (A-move-xy x y)

-- proofs inspired by these lecture notes
-- https://www.ruhr-uni-bochum.de/lmi/lehre/materialien/ti/vorlesung/ackermann.pdf
