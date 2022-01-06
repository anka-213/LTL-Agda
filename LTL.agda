{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --guardedness #-}

module LTL where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Sum
open import Relation.Nullary renaming (¬_ to ¬'_)
open import Data.Fin
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality


module Syntax (Atom : Set) where

  data ϕ : Set where
    -- atom     : Fin n → ϕ instantiate with module instead
    atom        : Atom → ϕ
    ⊥ ⊤         : ϕ
    ¬_          : ϕ → ϕ
    _∨_ _∧_ _⇒_ : ϕ → ϕ → ϕ
    X F G       : ϕ → ϕ
    _U_ _W_ _R_ : ϕ → ϕ → ϕ

  -- isSubForm : ϕ → ϕ → Set
  -- isSubForm ψ phi = {!phi \!}

open Syntax

rel : Set → Set₁
rel s = s → s → Set

-- power set
𝑃 : Set → Set
𝑃 s = s → Bool

-- 𝑃 Bool has four member
-- for example, we encode the empty set as follows
empt : 𝑃 Bool
empt false = false
empt true = false

relAlwaysSteps : {S : Set} → rel S → Set
relAlwaysSteps {S} rₛ = ∀ (s : S) → Σ[ s' ∈ S ] (rₛ s s')

module Transition (Atom : Set) (State : Set) (_⟶_ : rel State) where

  record 𝑀 : Set where
    field
      relSteps : relAlwaysSteps _⟶_
      L : State → 𝑃 Atom
      -- L : State → Atom → Bool

  record Stream : Set where
    coinductive
    -- constructor cons
    field
      hd : State
      tl : Stream

  open Stream

  nextState : Stream → State
  nextState s = hd (tl s)

  from-ithState : (i : ℕ) → Stream → Stream
  from-ithState zero x    = x
  from-ithState (suc i) x = from-ithState i (tl x)

  record streamAlwaysTransitions (stream : Stream) : Set where
    coinductive
    field
      headValid : hd stream ⟶ nextState stream
      tailValid : streamAlwaysTransitions (tl stream)

  record Path : Set where
    field
      infSeq         : Stream
      isTransitional : streamAlwaysTransitions infSeq

  open streamAlwaysTransitions
  open Path

  headPath : Path → State
  headPath x = hd (infSeq x)

  tailPath : Path → Path
  tailPath p .infSeq         = tl (infSeq p)
  tailPath p .isTransitional = tailValid (isTransitional p)

  -- drop : ℕ → Path → Path
  -- drop 0 x = x
  -- drop (suc n) x = tailPath (drop n x)

  module _ (M : 𝑀) where
    open 𝑀 M


    record G-pf (ψ : Path → Set) (π : Path) : Set where
      coinductive
      field
        ∀-h : ψ π
        ∀-t : G-pf ψ (tailPath π)

    data F-pf (P : Path → Set) (σ : Path) : Set where
      ev_h : P σ → F-pf P σ
      ev_t : F-pf P (tailPath σ) -> F-pf P σ

    data U-Pf (P Q : Path → Set) (σ : Path) : Set where
      until-h : Q σ → (U-Pf P Q) σ
      until-t : P σ → (U-Pf P Q) (tailPath σ) → (U-Pf P Q) σ

    data Uincl-Pf (P Q : Path → Set) (σ : Path) : Set where
      untilI-h : P σ → Q σ → (Uincl-Pf P Q) σ
      untilI-t : P σ → (Uincl-Pf P Q) (tailPath σ) → (Uincl-Pf P Q) σ

    _⊧_ : Path → ϕ Atom → Set
    π ⊧ ⊥        = ⊥'
    π ⊧ ⊤        = ⊤'
    π ⊧ atom x   = T (L (headPath π) x)
    π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
    π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
    π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
    π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
    π ⊧ X ψ      = tailPath π ⊧ ψ
    π ⊧ F ψ      = F-pf (_⊧ ψ) π
    π ⊧ G ψ      = G-pf (_⊧ ψ) π
    -- π ⊧ G ψ      = ∀ (n : ℕ) → drop n π ⊧ ψ
    π ⊧ (ψ U ψ₁) = U-Pf (_⊧ ψ) (_⊧ ψ₁) π
    π ⊧ (ψ W ψ₁) = (U-Pf (_⊧ ψ) (_⊧ ψ₁) π) ⊎ G-pf (_⊧ ψ) π
    π ⊧ (ψ R ψ₁) = Uincl-Pf (_⊧ ψ₁) (_⊧ ψ) π ⊎ G-pf (_⊧ ψ) π
    -- open Stream
    -- record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
    --   coinductive
    --   field
    --     hd-≈ : hd xs ≡ hd ys
    --     tl-≈ : tl xs ≈ tl ys

-- module Model (Atom : Set) (State : Set) where

    -- open Syntax Atom public
    -- open Transition Atom State
      --Definition 3.7
    _,_⊧_ : (M : 𝑀) → State → ϕ Atom → Set
    -- M , s ⊧ ψ = ∀ (p : Path M) → (π : pathStartsAt M p s) → _⊧_ M p ψ
    M , s ⊧ ψ = ∀ (p : Path) → p .infSeq .hd  ≡ s →  _⊧_ p ψ


module Example1 where

  data states : Set where
    s0 : states
    s1 : states
    s2 : states

  data atoms : Set where
    p : atoms
    q : atoms
    r : atoms

  data steps : rel states where
  -- data steps : states → states → Set where
    s0s1 : steps s0 s1
    s0s2 : steps s0 s2
    s1s0 : steps s1 s0
    s1s2 : steps s1 s2
    s2s2 : steps s2 s2

  steps-relAlwaysSteps : relAlwaysSteps steps
  steps-relAlwaysSteps s0 = s1 , s0s1
  steps-relAlwaysSteps s1 = s0 , s1s0
  steps-relAlwaysSteps s2 = s2 , s2s2

  l : states → 𝑃 atoms
  l s0 p = true
  l s0 q = true
  l s0 r = false
  l s1 p = false
  l s1 q = true
  l s1 r = true
  l s2 p = false
  l s2 q = false
  l s2 r = true

  open Transition atoms states steps
  open 𝑀

  ex1IsTransitionSyst : 𝑀
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L        = l

  open Path
  open Stream
  open streamAlwaysTransitions

  -- _◅_ : ∀ {i j k} (x : T i j) (xs : Star T j k) → Star T i k

  s2Stream : Stream
  s2Stream .hd = s2
  s2Stream .tl = s2Stream

  s2Transitions : streamAlwaysTransitions s2Stream
  s2Transitions .headValid = s2s2
  s2Transitions .tailValid = s2Transitions

  s2Path : Path
  s2Path .infSeq = s2Stream
  s2Path .isTransitional = s2Transitions
  -- s2Path .infSeq .hd = s2
  -- s2Path .infSeq .tl = s2Path .infSeq
  -- s2Path .isTransitional .headValid = s2s2
  -- s2Path .isTransitional .tailValid = s2Path .isTransitional

  -- rightmost branch on computation tree
  pathRight : Path
  pathRight .infSeq .hd = s0
  pathRight .infSeq .tl = s2Path .infSeq
  pathRight .isTransitional .headValid = s0s2
  pathRight .isTransitional .tailValid = s2Path .isTransitional


  seqLEven : Stream
  seqLOdd : Stream
  seqLEven .hd = s0
  seqLEven .tl = seqLOdd
  seqLOdd .hd = s1
  seqLOdd .tl = seqLEven

  transLEven : streamAlwaysTransitions seqLEven
  transLOdd : streamAlwaysTransitions seqLOdd
  transLEven .headValid = s0s1
  transLEven .tailValid = transLOdd
  transLOdd .headValid = s1s0
  transLOdd .tailValid = transLEven

  pathLeft : Path
  pathLeft .infSeq = seqLEven
  pathLeft .isTransitional = transLEven

  always-q-Left : _⊧_ ex1IsTransitionSyst pathLeft (atom q)
  always-q-Left = tt

  one : _,_⊧_ ex1IsTransitionSyst  ex1IsTransitionSyst s0 ((atom p) ∧ (atom q))
  one record { infSeq = infSeq ; isTransitional = isTransitional } = {!infSeq!}
  -- _,_⊧_ :


-- character references
-- 𝑀 == \MiM
-- 𝑃 == \MiP
