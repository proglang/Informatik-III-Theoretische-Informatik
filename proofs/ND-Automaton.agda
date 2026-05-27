module ND-Automaton where

open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; _++_; [_]) renaming (List to Word; [] to ε)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; swap; proj₁; proj₂) renaming (Σ to ΣΣ)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Unary using (Pred; _∈_; _∉_; _∩_; _∪_; Empty; ∅; ｛_｝)
  renaming (_⊆_ to _⊆′_; _≐_ to _≐′_)
open import Relation.Unary using () renaming (_⊆′_ to _⊆_; _≐′_ to _≐_)
open import Relation.Unary.Properties using (≐-sym)

open import Language
open import Sets

import Automaton as DET

-- nondeterministic automaton

record ND-Automaton (Σ : Set) : Set₁ where
  field
    Q      : Set
    δ      : Q → Σ → 𝔓 Q
    qinit  : Q
    F      : 𝔓 Q

  δ̃ : Q → Word Σ → 𝔓 Q
  δ̃ q ε        = ｛ q ｝
  δ̃ q (a ∷ w)  = ｛ p ∣ ∃[ q′ ] q′ ∈ δ q a × p ∈ δ̃ q′ w ｝

  accepts : Q → Language Σ
  accepts q w = F ∩ δ̃ q w ≠∅

  Lang : Language Σ
  Lang = accepts qinit

  reachable : 𝔓 Q
  reachable q = ∃[ w ] q ∈ δ̃ qinit w

-- utility

module _ {Σ : Set} (A : ND-Automaton Σ) where
  open ND-Automaton A

  δ̃-++ : ∀ (q : Q) (u : Word Σ) {v} → δ̃ q (u ++ v) ≐′ lift₂ δ̃ (δ̃ q u) v
  -- δ̃-++ : ∀ (q : Q) (u : Word Σ) {v} → δ̃ q (u ++ v) ≐′ lift (λ q′ → δ̃ q′ v) (δ̃ q u)

  δ̃-++ q ε .proj₁ x∈δ̃-q-v = q , refl , x∈δ̃-q-v
  δ̃-++ q (a ∷ u) .proj₁ (q′ , q′∈δ-q-a , x∈δ̃-q′-u++v) = let (q″ , q″∈δ̃-q′-u , ∈δ̃-q″-v) = δ̃-++ q′ u .proj₁ x∈δ̃-q′-u++v in  q″ , ((q′ , q′∈δ-q-a , q″∈δ̃-q′-u) , ∈δ̃-q″-v)

  δ̃-++ Q ε .proj₂ (q , refl , x∈δ̃-q-v) = x∈δ̃-q-v
  δ̃-++ q (a ∷ u) .proj₂ (q′ , (q″ , q″∈δ-q-a , q′∈δ̃-q″-u) , x∈δ̃-q′-v)
    = q″ , q″∈δ-q-a , δ̃-++ q″ u .proj₂ (q′ , q′∈δ̃-q″-u , x∈δ̃-q′-v)

-- powerset construction

module _ {Σ : Set} where
  powerset : ND-Automaton Σ → DET.Automaton Σ
  powerset 𝓝 = record {
    Q      =  𝔓 Qₙ ;
    δ      =  λ qq a → ｛ p ∣ ∃[ q ] q ∈ qq × p ∈ δₙ q a ｝ ;
    qinit  =  ｛ qinitₙ ｝ ;
    F      =  λ qq → Fₙ ∩ qq ≠∅
    }
    where open ND-Automaton 𝓝 renaming (Q to Qₙ; δ to δₙ; qinit to qinitₙ; F to Fₙ)

-- correctness proof of powerset construction

module Powerset {Σ : Set} (𝓝 :  ND-Automaton Σ) where
  open ND-Automaton 𝓝
  open DET.Automaton (powerset 𝓝) renaming (Q to Qₚ; δ to δₚ; δ̃ to δ̃ₚ; qinit to qinitₚ; accepts to acceptsₚ)

  -- monotonicity of δ

  δ-mono : (q1 q2 : Qₚ) → q1 ⊆′ q2 → ∀ a → δₚ q1 a ⊆′ δₚ q2 a
  δ-mono q1 q2 q1⊆q2 a (q , q∈q1 , x∈δ-q-a) = q , (q1⊆q2 q∈q1) , x∈δ-q-a

  δ̃-mono : (q1 q2 : Qₚ) → q1 ⊆′ q2 → ∀ w → δ̃ₚ q1 w ⊆′ δ̃ₚ q2 w
  δ̃-mono q1 q2 q1⊆q2 ε = q1⊆q2
  δ̃-mono q1 q2 q1⊆q2 (a ∷ w) x∈ = δ̃-mono (λ p → ∃[ q ] q ∈ q1 × p ∈ δ q a)
                                         (λ p → ∃[ q ] q ∈ q2 × p ∈ δ q a)
                                         (δ-mono q1 q2 q1⊆q2 a) w x∈

  power-left : (qn : Q) → (qd : Qₚ) → qn ∈ qd
    → accepts qn ⊆ acceptsₚ qd
  power-left qn qd qn∈qd ε (qf , qf∈F , refl) = qf , qf∈F , qn∈qd
  power-left qn qd qn∈qd (a ∷ w) (qf , qf∈F , (q′ , q′∈δ-qn-a , qf∈δ̃-q′-w))
    with power-left q′ (δ qn a) q′∈δ-qn-a w (qf , qf∈F , qf∈δ̃-q′-w)
  ... | qf' , qf'∈F , ih = qf' , qf'∈F , δ̃-mono (δ qn a) (λ p → ∃[ q ] q ∈ qd × p ∈ δ q a) (λ {x} z → qn , qn∈qd , z) w ih

  power-right : (qd : Qₚ)
    → ∀ w → acceptsₚ qd w → ∃[ qn ] qn ∈ qd × accepts qn w
  power-right qd ε (qf , qf∈F , qf∈dq) = qf , (qf∈dq , (qf , qf∈F , refl))
  power-right qd (a ∷ w) (qf , qf∈F , qf∈δ̃)
    with power-right (δₚ qd a) w ( qf , qf∈F , qf∈δ̃)
  ... | qi , (q0 , q0∈qd , qi∈δ-q-a) , (qf0 , qf0∈F , qf0∈δ̃-qi-w) = q0 , q0∈qd , qf0 , qf0∈F , (qi , qi∈δ-q-a , qf0∈δ̃-qi-w)

  correct : ND-Automaton.Lang 𝓝 ≐ DET.Automaton.Lang (powerset 𝓝)
  correct = power-left qinit qinitₚ refl
          , λ w x → case (power-right qinitₚ w x) of λ where
                      (q0 , refl , acc-q0-w) → acc-q0-w

-- ND automata constructions

module _ {Σ : Set} where

  δ∅ : ⊤ → Σ → 𝔓 ⊤
  δ∅ tt a tt = ⊥

  A∅ : ND-Automaton Σ
  A∅ = record { Q = ⊤ ; δ = δ∅ ; qinit = tt ; F = λ x → ⊥ }

  A∅-correct : ND-Automaton.Lang A∅ ≐ ∅
  A∅-correct .proj₁ w ()
  A∅-correct .proj₂ w ()

  δε : ⊤ → Σ → 𝔓 ⊤
  δε tt a tt = ⊥

  Aε : ND-Automaton Σ
  Aε = record { Q = ⊤ ; δ = δε ; qinit = tt ; F = tt ≡_ }

  Aε-correct : ND-Automaton.Lang Aε ≐ 𝟙
  Aε-correct .proj₁ ε x = tt
  Aε-correct .proj₁ (x₁ ∷ w) ()
  Aε-correct .proj₂ ε x = tt , refl , refl

  δa : Σ → Fin 2 → Σ → 𝔓 (Fin 2)
  δa a zero b zero = ⊥
  δa a zero b (suc zero) = a ≡ b
  δa a (suc zero) b x₃ = ⊥

  Aa : Σ → ND-Automaton Σ
  Aa a = record { Q = Fin 2 ; δ = δa a ; qinit = zero ; F = suc zero ≡_ }

  Aa-correct : ∀ a → ND-Automaton.Lang (Aa a) ≐ ｛ [ a ] ｝
  Aa-correct a .proj₁ ε (suc zero , refl , ())
  Aa-correct a .proj₁ (b ∷ ε) (suc zero , refl , suc zero , refl , refl) = refl
  Aa-correct a .proj₁ (b ∷ x₁ ∷ w) (suc zero , refl , suc zero , refl , fst₂ , () , snd)
  Aa-correct a .proj₂ (b ∷ ε) refl = suc zero , refl , (suc zero , refl , refl)

  module Concatenation (A₁ A₂ : ND-Automaton Σ) where
  
    open ND-Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁; δ̃ to δ̃₁; Lang to Lang₁)
    open ND-Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; F to F₂; δ̃ to δ̃₂; Lang to Lang₂)


    A· : ND-Automaton Σ
    A· = record {
      Q = Q₁ ⊎ Q₂ ;
      δ = λ{ (inj₁ q₁) a → λ{ (inj₁ q₁′) → q₁′ ∈ δ₁ q₁ a
                            ; (inj₂ q₂′) → q₁ ∈ F₁ × q₂′ ∈ δ₂ qinit₂ a }
           ; (inj₂ q₂) a → λ{ (inj₁ _) → ⊥
                            ; (inj₂ q₂′) → q₂′ ∈ δ₂ q₂ a } }  ;
      qinit = inj₁ qinit₁ ;
      F = λ{ (inj₁ x) → x ∈ F₁ × qinit₂ ∈ F₂
           ; (inj₂ y) → y ∈ F₂ }
      }

    open ND-Automaton A·

    A₁-sim : ∀ {q} q₁ w → q ∈ δ̃₁ q₁ w → inj₁ q ∈ δ̃ (inj₁ q₁) w
    A₁-sim q₁ ε refl = refl
    A₁-sim q₁ (a ∷ w) (q₁′ , q₁′∈δq₁a , q∈δ̃q₁′w) = (inj₁ q₁′) , (q₁′∈δq₁a , A₁-sim q₁′ w q∈δ̃q₁′w)

    A₂-sim : ∀ {q} q₂ w → q ∈ δ̃₂ q₂ w → inj₂ q ∈ δ̃ (inj₂ q₂) w
    A₂-sim q₂ ε refl = refl
    A₂-sim q₂ (a ∷ w) (q₂′ , q₂′∈δq₂a , q∈δ̃q₂′w) = (inj₂ q₂′) , q₂′∈δq₂a , A₂-sim q₂′ w q∈δ̃q₂′w

    A₂-sim⁺ : ∀ {q₂″} q a w → inj₁ q ∈ F → q₂″ ∈ δ̃₂ qinit₂ (a ∷ w) → inj₂ q₂″ ∈ δ̃ (inj₁ q) (a ∷ w)
    A₂-sim⁺ {q₂″} q a w (fst , snd) (q₂′ , q₂′∈δ₂qi-a , q₂″∈δ̃₂q₂′w) = let ih = A₂-sim q₂′ w q₂″∈δ̃₂q₂′w in inj₂ q₂′ , ((fst , q₂′∈δ₂qi-a) , ih)

    A₂-sim⁻ :  ∀ {q} q₂ w → inj₂ q ∈ δ̃ (inj₂ q₂) w → q ∈ δ̃₂ q₂ w
    A₂-sim⁻ q₂ ε refl = refl
    A₂-sim⁻ q₂ (a ∷ w) (inj₂ q₂′ , fst₁ , snd) = q₂′ , fst₁ , A₂-sim⁻ q₂′ w snd

    A·-inj₂ : ∀ q₁ q₂ w → inj₁ q₁ ∉ δ̃ (inj₂ q₂) w
    A·-inj₂ q₁ q₂ (a ∷ w) (inj₂ q₂′ , fst , snd) = A·-inj₂ q₁ q₂′ w snd

    A·-left : ∀ q₁ w → F ∩ δ̃ (inj₁ q₁) w ≠∅ → ∃[ u ] ∃[ v ] w ≡ u ++ v × F₁ ∩ δ̃₁ q₁ u ≠∅ × v ∈ Lang₂
    A·-left q₁ ε (inj₁ _ , (q₁∈F₁ , F₂-qi₂) , refl) = ε , ε , refl , (q₁ , q₁∈F₁ , refl) , (qinit₂ , F₂-qi₂ , refl)
    A·-left q₁ (a ∷ w) (q , q∈F , (inj₁ q₁′ , q₁′∈ , q∈δ̃-q′-w))
      with A·-left q₁′ w (q , q∈F , q∈δ̃-q′-w)
    ... | u , v , refl , (q₁″ , q₁″∈F₁ , ih) , ih₁ = (a ∷ u) , v , refl , (q₁″ , q₁″∈F₁ , (q₁′ , q₁′∈ , ih)) , ih₁
    A·-left q₁ (a ∷ w) (inj₁ x , q∈F , (inj₂ q₂′ , q₂′∈ , q∈δ̃-q′-w)) = contradiction q∈δ̃-q′-w (A·-inj₂ x q₂′ w)
    A·-left q₁ (a ∷ w) (inj₂ q , q∈F , (inj₂ q₂′ , q₂′∈ , q∈δ̃-q′-w)) = ε , (a ∷ w) , refl , (q₁ , q₂′∈ .proj₁ , refl) , q , (q∈F , q₂′ , ((q₂′∈ .proj₂) , (A₂-sim⁻ q₂′ w q∈δ̃-q′-w)))

    A·-correct : Lang ≐ (Lang₁ · Lang₂)
    A·-correct .proj₁ ε (inj₁ qinit₁ , (qi1∈F1 , qi2∈F2) , refl) = ε , ε , refl , (qinit₁ , qi1∈F1 , refl) , (qinit₂ , qi2∈F2 , refl)
    A·-correct .proj₁ (a ∷ w) w∈ = A·-left qinit₁ (a ∷ w) w∈

    A·-correct .proj₂ w (u , ε , refl , (q₁ , q₁∈F₁ , δ̃₁-qi-u-q₁) , (q₂ , q₂∈F₂ , refl))
      rewrite ++-identityʳ u = (inj₁ q₁) , (q₁∈F₁ , q₂∈F₂) , A₁-sim qinit₁ u δ̃₁-qi-u-q₁
    A·-correct .proj₂ w (u , a ∷ v , refl , (q₁ , q₁∈F₁ , δ̃₁-qi-u-q₁) , (q₂ , q₂∈F₂ , q₂′ , q₂′∈δ₂-qi2-a , q₂∈δ̃₂-q₂′-v))
      = (inj₂ q₂) , q₂∈F₂ , δ̃-++ A· (inj₁ qinit₁) u {a ∷ v} .proj₂
          ((inj₁ q₁) , A₁-sim qinit₁ u δ̃₁-qi-u-q₁
          , (inj₂ q₂′) , ((q₁∈F₁ , q₂′∈δ₂-qi2-a) , A₂-sim q₂′ v q₂∈δ̃₂-q₂′-v))

  module Kleene (A : ND-Automaton Σ) where
    open ND-Automaton A

    A* : ND-Automaton Σ
    A* = record {
      Q      = Word Σ ;
      δ      = λ u a → ｛ u ++ [ a ] ｝ ;
      qinit  = ε ;
      F      = Lang ∗
      }

    open ND-Automaton A* renaming (δ̃ to δ̃*; Lang to Lang*)

    δ̃*-append : ∀ u w → δ̃* u w ≐′ ｛ u ++ w ｝
    δ̃*-append u ε .proj₁ x∈ = trans (++-identityʳ u) x∈
    δ̃*-append u ε .proj₂ x∈ = trans (sym (++-identityʳ u)) x∈
    δ̃*-append u (a ∷ w) .proj₁ (. (u ++ [ a ]) , refl , x∈δ̃)
      rewrite sym (++-assoc u [ a ] w) = δ̃*-append (u ++ [ a ]) w .proj₁ x∈δ̃
    δ̃*-append u (a ∷ w) .proj₂ x∈
      rewrite sym (++-assoc u [ a ] w) = (u ++ [ a ]) , refl , δ̃*-append (u ++ [ a ]) w .proj₂ x∈

    A*-correct : ND-Automaton.Lang A* ≐ (Lang ∗)
    A*-correct .proj₁ w (u , u∈L* , u∈δ̃*)
      with δ̃*-append ε w .proj₁ u∈δ̃*
    ... | refl = u∈L*
    A*-correct .proj₂ w w∈L* = w , w∈L* , δ̃*-append ε w .proj₂ refl

  module Kleene2 (A : ND-Automaton Σ) where
    open ND-Automaton A

    A* : ND-Automaton Σ
    A* = record {
      Q      = ⊤ ⊎ Q ;
      δ      = λ{ (inj₁ tt) a → λ{ (inj₁ _) → ⊥
                                 ; (inj₂ q′) → q′ ∈ δ qinit a }
               ; (inj₂ q) a → λ{ (inj₁ _) → ⊥
                                ; (inj₂ q′) → q′ ∈ δ q a ⊎ (q ∈ F × q′ ∈ δ qinit a) } } ;
      qinit  = inj₁ tt ;
      F      = λ{ (inj₁ _) → ⊤
               ; (inj₂ q) → q ∈ F }
      }

    open ND-Automaton A* renaming (Q to Q*; δ to δ*; qinit to qinit*; F to F*; δ̃ to δ̃*; accepts to accepts*; Lang to Lang*)

    finite-Q* : Finite Q → Finite Q*
    finite-Q* (n , iso) = suc n , record {
      fwd = λ{ (inj₁ tt) → zero
             ; (inj₂ q) → suc (Iso.fwd iso q) } ;
      bwd = λ{ zero → inj₁ tt
             ; (suc i) → inj₂ (Iso.bwd iso i) } ;
      fwd∘bwd = λ{ zero → refl
                 ; (suc i) → cong suc (Iso.fwd∘bwd iso i) } ;
      bwd∘fwd = λ{ (inj₁ tt) → refl
                 ; (inj₂ q) → cong inj₂ (Iso.bwd∘fwd iso q) }
      }

    Acc₂ : Q → Language Σ
    Acc₂ q w = F* ∩ δ̃* (inj₂ q) w ≠∅

    acc-left : ∀ q w → Acc₂ q w → (accepts q · (Lang ∗)) w
    acc-left q ε (inj₂ .q , q∈F , refl) = ε , ε , refl , (q , q∈F , refl) , (zero , tt)
    acc-left q (a ∷ w) (r , r∈F* , (inj₂ q₁ , inj₁ q₁∈δqa , r∈δ̃))
      with acc-left q₁ w (r , r∈F* , r∈δ̃)
    ... | u , v , w≡u++v , (qf , qf∈F , qf∈δ̃q₁u) , v∈Lang*
      = (a ∷ u) , v , cong (_∷_ a) w≡u++v
      , (qf , qf∈F , (q₁ , q₁∈δqa , qf∈δ̃q₁u))
      , v∈Lang*
    acc-left q (a ∷ w) (r , r∈F* , (inj₂ q₁ , inj₂ (q∈F , q₁∈δqinita) , r∈δ̃))
      with acc-left q₁ w (r , r∈F* , r∈δ̃)
    ... | u , v , w≡u++v , (qf , qf∈F , qf∈δ̃q₁u) , (n , v∈Lang↑n)
      = ε , (a ∷ w) , refl
      , (q , q∈F , refl)
      , subst (Lang ∗) (sym (cong (_∷_ a) w≡u++v))
          (suc n
          , (a ∷ u) , v , refl
          , (qf , qf∈F , (q₁ , q₁∈δqinita , qf∈δ̃q₁u))
          , v∈Lang↑n)

    star-left : ∀ w → w ∈ Lang* → w ∈ (Lang ∗)
    star-left ε (inj₁ tt , tt , refl) = zero , tt
    star-left (a ∷ w) (r , r∈F* , (inj₂ q₁ , q₁∈δqinita , r∈δ̃))
      with acc-left q₁ w (r , r∈F* , r∈δ̃)
    ... | u , v , w≡u++v , (qf , qf∈F , qf∈δ̃q₁u) , (n , v∈Lang↑n)
      = suc n
      , (a ∷ u) , v , cong (_∷_ a) w≡u++v
      , (qf , qf∈F , (q₁ , q₁∈δqinita , qf∈δ̃q₁u))
      , v∈Lang↑n

    mutual
      star-right↑ : ∀ n w → w ∈ (Lang ↑ n) → w ∈ Lang*
      star-right↑ zero ε tt = inj₁ tt , tt , refl
      star-right↑ zero (a ∷ w) ()
      star-right↑ (suc n) w (u , v , w≡u++v , u∈Lang , v∈Lang↑n)
        with u | u∈Lang
      ... | ε | (qf , qf∈F , refl)
        = subst Lang* (sym w≡u++v) (star-right↑ n v v∈Lang↑n)
      ... | a ∷ u' | (qf , qf∈F , q₁ , q₁∈δqinita , qf∈δ̃q₁u')
        = subst Lang* (sym w≡u++v)
            (r , r∈F*
            , (inj₂ q₁ , q₁∈δqinita , r∈δ̃*))
        where
          r : Q*
          r = proj₁ (acc-right↑ n q₁ u' v (qf , qf∈F , qf∈δ̃q₁u') v∈Lang↑n)

          r∈F* : r ∈ F*
          r∈F* = proj₁ (proj₂ (acc-right↑ n q₁ u' v (qf , qf∈F , qf∈δ̃q₁u') v∈Lang↑n))

          r∈δ̃* : r ∈ δ̃* (inj₂ q₁) (u' ++ v)
          r∈δ̃* = proj₂ (proj₂ (acc-right↑ n q₁ u' v (qf , qf∈F , qf∈δ̃q₁u') v∈Lang↑n))

      acc-right↑ : ∀ n q u v → accepts q u → v ∈ (Lang ↑ n) → Acc₂ q (u ++ v)
      acc-right↑ n q ε v (qf , qf∈F , refl) v∈Lang↑n with v
      ... | ε = inj₂ q , qf∈F , refl
      ... | a ∷ v'
        with star-right↑ n (a ∷ v') v∈Lang↑n
      ... | r , r∈F* , (inj₂ q₁ , q₁∈δqinita , r∈δ̃*)
        = r , r∈F* , (inj₂ q₁ , inj₂ (qf∈F , q₁∈δqinita) , r∈δ̃*)
      acc-right↑ n q (a ∷ u) v (qf , qf∈F , q₁ , q₁∈δqa , qf∈δ̃q₁u) v∈Lang↑n
        with acc-right↑ n q₁ u v (qf , qf∈F , qf∈δ̃q₁u) v∈Lang↑n
      ... | r , r∈F* , r∈δ̃*
        = r , r∈F* , (inj₂ q₁ , inj₁ q₁∈δqa , r∈δ̃*)

    star-right : ∀ w → w ∈ (Lang ∗) → w ∈ Lang*
    star-right w (n , w∈Lang↑n) = star-right↑ n w w∈Lang↑n

    A*-correct : ND-Automaton.Lang A* ≐ (Lang ∗)
    A*-correct = star-left , star-right

  module Union (A₁ A₂ : ND-Automaton Σ) where
    open ND-Automaton A₁ renaming (Q to Q₁; δ to δ₁; qinit to qinit₁; F to F₁; δ̃ to δ̃₁; Lang to Lang₁)
    open ND-Automaton A₂ renaming (Q to Q₂; δ to δ₂; qinit to qinit₂; F to F₂; δ̃ to δ̃₂; Lang to Lang₂)

    A∪ : ND-Automaton Σ
    A∪ = record
      { Q = ⊤ ⊎ (Q₁ ⊎ Q₂)
      ; δ = λ{ (inj₁ tt) a → λ{ (inj₁ x) → ⊥
                              ; (inj₂ (inj₁ x)) → x ∈ δ₁ qinit₁ a
                              ; (inj₂ (inj₂ y)) → y ∈ δ₂ qinit₂ a }
             ; (inj₂ (inj₁ q₁)) a → λ{ (inj₁ x) → ⊥
                                    ; (inj₂ (inj₁ q₁′)) → q₁′ ∈ δ₁ q₁ a 
                                    ; (inj₂ (inj₂ q₂′)) → ⊥ }
             ; (inj₂ (inj₂ q₂)) a → λ{ (inj₁ x) → ⊥
                                     ; (inj₂ (inj₁ q₁′)) → ⊥
                                     ; (inj₂ (inj₂ q₂′)) → q₂′ ∈ δ₂ q₂ a }
             }
      ; qinit = inj₁ tt
      ; F = λ{ (inj₁ x) → qinit₁ ∈ F₁ ⊎ qinit₂ ∈ F₂
             ; (inj₂ (inj₁ q₁)) → q₁ ∈ F₁
             ; (inj₂ (inj₂ q₂)) → q₂ ∈ F₂ }
      }

    open ND-Automaton A∪

    A∪-sim₁ : ∀ q q′ w 
      → (inj₂ (inj₁ q′)) ∈ δ̃ (inj₂ (inj₁ q)) w
      → q′ ∈ δ̃₁ q w
    A∪-sim₁ q q′ ε refl = refl
    A∪-sim₁ q q′ (a ∷ w) (inj₂ (inj₁ q₁) , q₁∈δ₁-q-a , δ̃-q₁-w)
      = q₁ , q₁∈δ₁-q-a , A∪-sim₁ q₁ q′ w δ̃-q₁-w

    A∪-sim₂ : ∀ q q′ w
      → (inj₂ (inj₂ q′)) ∈ δ̃ (inj₂ (inj₂ q)) w
      → q′ ∈ δ̃₂ q w
    A∪-sim₂ q q′ ε refl = refl
    A∪-sim₂ q q′ (a ∷ w) (inj₂ (inj₂ q₂) , q₂∈δ₂-q-a , δ̃-q₂-w)
      = q₂ , q₂∈δ₂-q-a , A∪-sim₂ q₂ q′ w δ̃-q₂-w

    A∪-sim₁⁺ : ∀ q q′ w
      → q′ ∈ δ̃₁ q w
      → (inj₂ (inj₁ q′)) ∈ δ̃ (inj₂ (inj₁ q)) w
    A∪-sim₁⁺ q q′ ε refl = refl
    A∪-sim₁⁺ q q′ (a ∷ w) (q₁ , q₁∈δ₁-q-a , δ̃-q₁-w)
      = (inj₂ (inj₁ q₁)) , q₁∈δ₁-q-a , A∪-sim₁⁺ q₁ q′ w δ̃-q₁-w

    A∪-sim₂⁺ : ∀ q q′ w
      → q′ ∈ δ̃₂ q w
      → (inj₂ (inj₂ q′)) ∈ δ̃ (inj₂ (inj₂ q)) w
    A∪-sim₂⁺ q q′ ε refl = refl
    A∪-sim₂⁺ q q′ (a ∷ w) (q₂ , q₂∈δ₂-q-a , δ̃-q₂-w)
      = (inj₂ (inj₂ q₂)) , q₂∈δ₂-q-a , A∪-sim₂⁺ q₂ q′ w δ̃-q₂-w

    A∪-no-tt₁ : ∀ q w → inj₁ tt ∉ δ̃ (inj₂ (inj₁ q)) w
    A∪-no-tt₁ q ε ()
    A∪-no-tt₁ q (a ∷ w) (q′ , q′∈δ-a , tt∈δ̃-q′-w) with q′
    ... | inj₁ tt = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₁ q₁′) = A∪-no-tt₁ q₁′ w tt∈δ̃-q′-w
    ... | inj₂ (inj₂ q₂′) = contradiction q′∈δ-a (λ ())

    A∪-no-tt₂ : ∀ q w → inj₁ tt ∉ δ̃ (inj₂ (inj₂ q)) w
    A∪-no-tt₂ q ε ()
    A∪-no-tt₂ q (a ∷ w) (q′ , q′∈δ-a , tt∈δ̃-q′-w) with q′
    ... | inj₁ tt = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₁ q₁′) = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₂ q₂′) = A∪-no-tt₂ q₂′ w tt∈δ̃-q′-w

    A∪-no-12 : ∀ q₁ q₂ w → inj₂ (inj₂ q₂) ∉ δ̃ (inj₂ (inj₁ q₁)) w
    A∪-no-12 q₁ q₂ ε ()
    A∪-no-12 q₁ q₂ (a ∷ w) (q′ , q′∈δ-a , q₂∈δ̃-q′-w) with q′
    ... | inj₁ tt = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₁ q₁′) = A∪-no-12 q₁′ q₂ w q₂∈δ̃-q′-w
    ... | inj₂ (inj₂ q₂′) = contradiction q′∈δ-a (λ ())

    A∪-no-21 : ∀ q₂ q₁ w → inj₂ (inj₁ q₁) ∉ δ̃ (inj₂ (inj₂ q₂)) w
    A∪-no-21 q₂ q₁ ε ()
    A∪-no-21 q₂ q₁ (a ∷ w) (q′ , q′∈δ-a , q₁∈δ̃-q′-w) with q′
    ... | inj₁ tt = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₁ q₁′) = contradiction q′∈δ-a (λ ())
    ... | inj₂ (inj₂ q₂′) = A∪-no-21 q₂′ q₁ w q₁∈δ̃-q′-w

    A∪-correct : Lang ≐ Lang₁ ∪ Lang₂
    A∪-correct .proj₁ ε (inj₁ tt , inj₁ qinit₁∈F₁ , refl) = inj₁ (qinit₁ , qinit₁∈F₁ , refl)
    A∪-correct .proj₁ ε (inj₁ tt , inj₂ qinit₂∈F₂ , refl) = inj₂ (qinit₂ , qinit₂∈F₂ , refl)
    A∪-correct .proj₁ (a ∷ w) (qf , qf∈F , inj₁ tt , q0∈δ-a , qf∈δ̃)
      = contradiction q0∈δ-a (λ ())
    A∪-correct .proj₁ (a ∷ w) (inj₁ tt , qf∈F , inj₂ (inj₁ q₁) , q0∈δ-a , qf∈δ̃)
      = contradiction qf∈δ̃ (A∪-no-tt₁ q₁ w)
    A∪-correct .proj₁ (a ∷ w) (inj₂ (inj₁ q₁′) , qf∈F , inj₂ (inj₁ q₁) , q0∈δ-a , qf∈δ̃)
      = inj₁ (q₁′ , qf∈F , q₁ , q0∈δ-a , A∪-sim₁ q₁ q₁′ w qf∈δ̃)
    A∪-correct .proj₁ (a ∷ w) (inj₂ (inj₂ q₂′) , qf∈F , inj₂ (inj₁ q₁) , q0∈δ-a , qf∈δ̃)
      = contradiction qf∈δ̃ (A∪-no-12 q₁ q₂′ w)
    A∪-correct .proj₁ (a ∷ w) (inj₁ tt , qf∈F , inj₂ (inj₂ q₂) , q0∈δ-a , qf∈δ̃)
      = contradiction qf∈δ̃ (A∪-no-tt₂ q₂ w)
    A∪-correct .proj₁ (a ∷ w) (inj₂ (inj₁ q₁′) , qf∈F , inj₂ (inj₂ q₂) , q0∈δ-a , qf∈δ̃)
      = contradiction qf∈δ̃ (A∪-no-21 q₂ q₁′ w)
    A∪-correct .proj₁ (a ∷ w) (inj₂ (inj₂ q₂′) , qf∈F , inj₂ (inj₂ q₂) , q0∈δ-a , qf∈δ̃)
      = inj₂ (q₂′ , qf∈F , q₂ , q0∈δ-a , A∪-sim₂ q₂ q₂′ w qf∈δ̃)

    A∪-correct .proj₂ ε (inj₁ (qf , qf∈F₁ , refl)) = inj₁ tt , inj₁ qf∈F₁ , refl
    A∪-correct .proj₂ ε (inj₂ (qf , qf∈F₂ , refl)) = inj₁ tt , inj₂ qf∈F₂ , refl
    A∪-correct .proj₂ (a ∷ w) (inj₁ (qf , qf∈F₁ , q₁ , q₁∈δ₁-a , qf∈δ̃₁))
      = inj₂ (inj₁ qf) , qf∈F₁ , inj₂ (inj₁ q₁) , q₁∈δ₁-a , A∪-sim₁⁺ q₁ qf w qf∈δ̃₁
    A∪-correct .proj₂ (a ∷ w) (inj₂ (qf , qf∈F₂ , q₂ , q₂∈δ₂-a , qf∈δ̃₂))
      = inj₂ (inj₂ qf) , qf∈F₂ , inj₂ (inj₂ q₂) , q₂∈δ₂-a , A∪-sim₂⁺ q₂ qf w qf∈δ̃₂
