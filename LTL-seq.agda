{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --no-positivity-check #-}

module LTL-seq where

open import Data.Bool renaming (_∨_ to _∨'_ ; _∧_ to _∧'_)
open import Data.Nat renaming (_≤_ to _≤'_ ; _<_ to _<'_)
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

  open 𝑀

  alwaysSteps : (sₙ : ℕ → State) → Set
  alwaysSteps s = ∀ i → s i ⟶ s (suc i)

  record Path : Set where
    field
      infSeq         : ℕ → State
      isTransitional : alwaysSteps infSeq

  -- open streamAlwaysTransitions
  open Path

  headPath : Path → State
  headPath record { infSeq = infSeq ; isTransitional = isTransitional } = infSeq 0
  -- headPath p = {!!}
  -- headPath p = {!!}

  tailPath : Path → Path
  tailPath record { infSeq = infSeq ; isTransitional = isTransitional } .Path.infSeq x = infSeq (suc x)
  tailPath record { infSeq = infSeq ; isTransitional = isTransitional } .Path.isTransitional i = isTransitional (suc i)

  path-i : ℕ → Path → Path
  path-i zero p = p
  path-i (suc i) p = path-i i (tailPath p)

  -- path-i (suc i) record { infSeq = infSeq ; isTransitional = isTransitional } .Path.infSeq = {!!}
  -- path-i (suc i) record { infSeq = infSeq ; isTransitional = isTransitional } .Path.isTransitional = {!!}
  -- path-i zero p .infSeq            = {!!}
  -- path-i zero p .isTransitional    = {!!}
  -- path-i (suc i) p .infSeq         = {!!}
  -- path-i (suc i) p .isTransitional = {!!}

  module _ (M : 𝑀) where
    open 𝑀 M

    mutual

      future : Path → ϕ Atom → Set
      future π ψ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ

      global : Path → ϕ Atom → Set
      global π ψ = ∀ i → (path-i i π) ⊧ ψ

      justUpTil : ℕ → Path → ϕ Atom → Set
      justUpTil i π ψ = (∀ (j : ℕ) → j <' i → (path-i j π) ⊧ ψ)

      upTil : ℕ → Path → ϕ Atom → Set
      upTil i π ψ = (∀ (j : ℕ) → j ≤' i → (path-i j π) ⊧ ψ)

      -- can rewrite with future in first clause
      justUntil : Path → ϕ Atom → ϕ Atom → Set
      justUntil π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × justUpTil i π ψ

      until : Path → ϕ Atom → ϕ Atom → Set
      until π ψ ψ₁ = Σ[ i ∈ ℕ ] (path-i i π) ⊧ ψ₁ × upTil i π ψ

      _⊧_ : Path → ϕ Atom → Set
      π ⊧ ⊥        = ⊥'
      π ⊧ ⊤        = ⊤'
      π ⊧ atom p   = T (L {!!}) -- ⊤' -- T {!!} -- T (L (headPath π) p)
      π ⊧ (¬ ψ)    = ¬' (π ⊧ ψ)
      π ⊧ (ψ ∨ ψ₁) = (π ⊧ ψ) ⊎ (π ⊧ ψ₁)
      π ⊧ (ψ ∧ ψ₁) = (π ⊧ ψ) × (π ⊧ ψ₁)
      π ⊧ (ψ ⇒ ψ₁) = (π ⊧ ψ) → (π ⊧ ψ₁)
      π ⊧ X ψ      = tailPath π ⊧ ψ
      π ⊧ F ψ      = future π ψ
      π ⊧ G ψ      = global π ψ
      π ⊧ (ψ U ψ₁) = justUntil π ψ ψ₁
      π ⊧ (ψ W ψ₁) = justUntil π ψ ψ₁ ⊎ global π ψ
      π ⊧ (ψ R ψ₁) = until π ψ₁ ψ ⊎ global π ψ

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

  open Transition atoms
  open 𝑀

  ex1IsTransitionSyst : 𝑀 states steps
  ex1IsTransitionSyst .relSteps = steps-relAlwaysSteps
  ex1IsTransitionSyst .L        = l


-- character references
-- 𝑀 == \MiM
-- 𝑃 == \MiP
