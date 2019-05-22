module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Exercise seven
-- Write out 7 in longhand.
-- suc (suc (suc (suc (suc (suc (suc zero)))))) : ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

infixl 6  _+_  _∸_
infixl 7  _*_

-- addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- interactively written addition
-- _++_ : ℕ → ℕ → ℕ
-- zero ++ n = n
-- suc m ++ n = suc (m + n)

-- addition example proof (verbose)
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

-- addition example (succinct)
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- by simplification
_ : 2 + 3 ≡ 5
_ = refl

-- Exercise +-example
-- Compute 3 + 4, writing out your reasoning as a chain of equations.

-- long addition
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

-- by simplification
_ : 3 + 4 ≡ 7
_ = refl

-- multiplication
_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

  -- Exercise *-example
  -- Compute 3 * 4, writing out your reasoning as a chain of equations.
_ =
  begin
    3 * 4
  ≡⟨⟩    -- inductive case
    4 + (2 * 4)
  ≡⟨⟩    -- inductive case
    4 + (4 + (1 * 4))
  ≡⟨⟩    -- inductive case
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩    -- base case
    4 + (4 + (4 + 0))
  ≡⟨⟩    -- simplify
    12
  ∎


--
-- Exercise _^_ (recommended)
-- Define exponentiation, which is given by the following equations:
--
-- n ^ 0        =  1
-- n ^ (1 + m)  =  n * (n ^ m)

-- exponentiation
_^_ : ℕ → ℕ → ℕ
n ^ zero  =  1
n ^ suc m =  n * (n ^ m)

-- Check that 3 ^ 4 is 81.
_ =
  begin
    3 ^ 4
  ≡⟨⟩    -- inductive case
    3 * (3 ^ 3)
  ≡⟨⟩    -- inductive case
    3 * (3 * (3 ^ 2))
  ≡⟨⟩    -- inductive case
    3 * (3 * (3  * (3 ^ 1)))
  ≡⟨⟩    -- base case
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩    -- simplify
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩    -- simplify
    81
  ∎

-- monus

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
     3 ∸ 2
  ≡⟨⟩
     2 ∸ 1
  ≡⟨⟩
     1 ∸ 0
  ≡⟨⟩
     1
  ∎

_ =
  begin
     2 ∸ 3
  ≡⟨⟩
     1 ∸ 2
  ≡⟨⟩
     0 ∸ 1
  ≡⟨⟩
     0
  ∎


  -- Exercise ∸-examples (recommended)
  -- Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.

_ =
  begin
     5 ∸ 3
  ≡⟨⟩
     4 ∸ 2
  ≡⟨⟩
     2 ∸ 0
  ≡⟨⟩
     2
  ∎

_ =
  begin
     3 ∸ 5
  ≡⟨⟩
     2 ∸ 4
  ≡⟨⟩
     0 ∸ 2
  ≡⟨⟩
     0
  ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

  -- Exercise Bin (stretch)
  -- A more efficient representation of natural numbers uses a binary
  -- rather than a unary system. We represent a number as a bitstring:

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 (inc m)

-- inc 0 = 1
_ : inc (nil) ≡ x1 nil
_ = refl

-- inc 1 = 2 ...
_ : inc (x1 nil) ≡ x0 (x1 nil)
_ = refl

_ : inc (x0 (x1 nil)) ≡ x1 (x1 nil)
_ = refl

_ : inc (x1 (x1 nil)) ≡ x0 (x0 (x1 nil))
_ = refl

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

--- TODO

-- to   : ℕ → Bin
-- from : Bin → ℕ
