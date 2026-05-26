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
open import Relation.Unary using (Pred; _∈_; _∉_;_∩_; Empty; ｛_｝) renaming (_⊆_ to _⊆′_; _≐_ to _≐′_)
open import Relation.Unary.Properties using (≐-sym)

open import Language hiding (_∩_) renaming (｛_｝ to singleton )
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

  δ̃-++ : ∀ (q : Q) (u : Word Σ) {v} → δ̃ q (u ++ v) ≐′ lift (λ q′ → δ̃ q′ v) (δ̃ q u)

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

  Aa-correct : ∀ a → ND-Automaton.Lang (Aa a) ≐ singleton [ a ]
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

    A·-left : ∀ q₁ w → δ̃ (inj₁ q₁) w ∩ F ≠∅ → ∃[ u ] ∃[ v ] w ≡ u ++ v × δ̃₁ q₁ u ∩ F₁ ≠∅ × v ∈ Lang₂
    A·-left q₁ ε (inj₁ _ , refl , q₁∈F₁ , F₂-qi₂) = ε , ε , refl , (q₁ , refl , q₁∈F₁) , (qinit₂ , F₂-qi₂ , refl)
    A·-left q₁ (a ∷ w) (q , (inj₁ q₁′ , q₁′∈ , q∈δ̃-q′-w) , q∈F)
      with A·-left q₁′ w (q , q∈δ̃-q′-w , q∈F)
    ... | u , v , refl , (q₁″ , ih , q₁″∈F₁) , ih₁ = (a ∷ u) , v , refl , (q₁″ , (q₁′ , q₁′∈ , ih) , q₁″∈F₁) , ih₁
    A·-left q₁ (a ∷ w) (inj₁ x , (inj₂ q₂′ , q₂′∈ , q∈δ̃-q′-w) , q∈F) = contradiction q∈δ̃-q′-w (A·-inj₂ x q₂′ w)
    A·-left q₁ (a ∷ w) (inj₂ q , (inj₂ q₂′ , q₂′∈ , q∈δ̃-q′-w) , q∈F) = ε , (a ∷ w) , refl , (q₁ , refl , q₂′∈ .proj₁) , q , (q∈F , q₂′ , ((q₂′∈ .proj₂) , (A₂-sim⁻ q₂′ w q∈δ̃-q′-w)))

    A·-correct : Lang ≐ (Lang₁ · Lang₂)
    
    A·-correct .proj₁ ε (inj₁ qinit₁ , (qi1∈F1 , qi2∈F2) , refl) = ε , ε , refl , ((qinit₁ , qi1∈F1 , refl) , (qinit₂ , (qi2∈F2 , refl)))
    A·-correct .proj₁ (a ∷ w) w∈ = {!A·-left qinit₁ (a ∷ w) !}
    
    A·-correct .proj₂ w (u , ε , refl , u∈LA₁@(q₁ , q₁∈F₁ , δ̃₁-qi-u-q₁) , v∈LA₂@(q₂ , q₂∈F₂ , refl))
      rewrite ++-identityʳ u = (inj₁ q₁) , (q₁∈F₁ , q₂∈F₂) , A₁-sim qinit₁ u δ̃₁-qi-u-q₁
    A·-correct .proj₂ w (u , a ∷ v , refl , u∈LA₁@(q₁ , q₁∈F₁ , δ̃₁-qi-u-q₁) , v∈LA₂@ (q₂ , q₂∈F₂ , (q₂′ , q₂′∈δ₂-qi2-a , q₂∈δ̃₂-q₂′-v)))
      = (inj₂ q₂) , (q₂∈F₂ , δ̃-++ A· (inj₁ qinit₁) u {a ∷ v} .proj₂ {inj₂ q₂} {!!})
