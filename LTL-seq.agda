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

mutual
  even : ℕ → Bool
  even zero = true
  even (suc x) = odd x

  odd : ℕ → Bool
  odd zero = false
  odd (suc zero) = true
  odd (suc (suc n)) = even (suc n)

open Syntax
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

  open Path

  headPath : Path → State
  headPath p = p .infSeq 0

  tailPath : Path → Path
  tailPath p .infSeq x = p .infSeq (suc x)
  tailPath p .isTransitional i = p .isTransitional (suc i)

  -- path-i == drop
  path-i : ℕ → Path → Path
  path-i zero p = p
  path-i (suc i) p = path-i i (tailPath p)

  -- module _ (M : 𝑀) where
  --   open 𝑀 M

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

    -- Definition 3.6
    _⊧_ : Path → ϕ Atom → Set
    π ⊧ ⊥        = ⊥'
    π ⊧ ⊤        = ⊤'
    π ⊧ atom p   = ⊤' -- T (L {!!}) -- ⊤' -- T {!!} -- T (L (headPath π) p)
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

  open Path
  -- rightmost branch on computation tree
  pathRight : Path states steps
  pathRight .infSeq zero = s0
  pathRight .infSeq (suc i) = s2
  pathRight .isTransitional zero = s0s2
  pathRight .isTransitional (suc i) = s2s2

  -- how to do coinduction
  pathLeft : Path states steps
  pathLeft .infSeq zero = s0
  pathLeft .infSeq (suc zero) = s1
  pathLeft .infSeq (suc (suc x)) = pathLeft .infSeq x
  pathLeft .isTransitional zero = s0s1
  pathLeft .isTransitional (suc zero) = s1s0
  pathLeft .isTransitional (suc (suc i)) = pathLeft .isTransitional i

  -- pathLeftOdd : Path states steps
  -- pathLeft .infSeq zero = s0
  -- pathLeft .infSeq (suc x) = pathLeftOdd .infSeq x
  -- pathLeft .isTransitional zero = {!s0s1!}
  -- pathLeft .isTransitional (suc i) = pathLeftOdd .isTransitional i
  -- pathLeftOdd .infSeq zero = s1
  -- pathLeftOdd .infSeq (suc x) = pathLeft .infSeq x
  -- pathLeftOdd .isTransitional zero = {!s1s0!}
  -- pathLeftOdd .isTransitional (suc i) = pathLeft .isTransitional i

  -- pathLeft .infSeq x = if (even x) then s0 else s1
  -- -- pathLeft .infSeq (suc zero) = {!!}
  -- -- pathLeft .infSeq (suc (suc i)) = {!!}
  -- pathLeft .isTransitional n with even n | odd n
  -- pathLeft .isTransitional n | false | false = {!!}
  -- pathLeft .isTransitional n | false | true = s1s0
  -- pathLeft .isTransitional n | true | false = s0s1
  -- pathLeft .isTransitional n | true | true = {!!}
  -- -- pathLeft .isTransitional zero = s0s1
  -- -- pathLeft .isTransitional (suc zero) = s1s0
  -- -- pathLeft .isTransitional (suc (suc i)) = let x = (path-i states steps i pathLeft) in {!Transition.Path.isTransitional!}
  -- -- ... | false = {!!}
  -- -- ... | true = {!!}
  

  -- ⊧_


-- character references
-- 𝑀 == \MiM
-- 𝑃 == \MiP
