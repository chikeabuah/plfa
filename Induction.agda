module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

  -- associativity

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
   zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- commutativity

-- first lemma: zero is a right identity

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎


-- second lemma: push `suc` on 2nd argument to outside
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- addition: proof
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- third lemma: multiplication property of zero on the right

*-mult0ʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-mult0ʳ zero =
  begin
    zero * zero
  ≡⟨⟩
    zero
  ∎
*-mult0ʳ (suc m) =
  begin
    suc m * zero
  ≡⟨⟩
    zero + (m * zero)
  ≡⟨ cong (zero +_) (*-mult0ʳ m) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

-- We can apply associativity to rearrange parentheses however we like.
-- Here is an example:

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- associativity 2
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

-- commutativity 2
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercise +-swap (recommended)
-- Show m + (n + p) ≡ n + (m + p)
-- first proof in agda :)

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

--
-- Exercise *-distrib-+ (recommended)
-- Show multiplication distributes over addition, that is,
--
-- (m + n) * p ≡ m * p + n * p
-- for all naturals m, n, and p.

-- Your code goes here

-- second lemma: inductive property of multiplication on the right
-- with the product "reversed"
*-indʳ : ∀ (m n : ℕ) → n * suc m ≡ n + (n * m)
*-indʳ m zero =
  begin
    zero * suc m
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨⟩
    zero + (zero * m)
  ∎
*-indʳ m (suc n) =
  begin
    suc n * suc m
  ≡⟨⟩
    suc m + (n * suc m)
  ≡⟨ cong ((suc m) +_) (*-indʳ m n) ⟩
    (suc m) + (n + (n * m))
  ≡⟨⟩
    suc (m + (n + (n * m)))
  ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
    suc (m + n + (n * m))
  ≡⟨ cong suc (cong (_+ (n * m)) (+-comm m n)) ⟩
    suc (n + m + (n * m))
  ≡⟨ cong suc (+-assoc n m (n * m)) ⟩
    suc (n + (m + (n * m)))
  ≡⟨⟩
    suc n + (m + (n * m))
  ≡⟨⟩
    suc n + (suc n * m)
  ∎

--

-- commutativity: multiplication
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-mult0ʳ n) ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    (suc m) * n
  ≡⟨⟩
    n + (m * n)
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + (n * m)
  ≡⟨ sym (*-indʳ m n) ⟩
    n * (suc m)
  ∎

--
-- third lemma: inductive property of multiplication on the right
-- "not reversed"
*-indʳ₁ : ∀ (m n : ℕ) → n * suc m ≡ n + (m * n)
*-indʳ₁ m zero =
  begin
    zero * suc m
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨ cong (zero +_) (sym (*-mult0ʳ m)) ⟩
    zero + (m * zero)
  ∎
*-indʳ₁ m (suc n) =
  begin
    suc n * suc m
  ≡⟨⟩
    suc m + (n * suc m)
  ≡⟨ cong ((suc m) +_) (*-indʳ₁ m n) ⟩
    (suc m) + (n + (m * n))
  ≡⟨⟩
    suc (m + (n + (m * n)))
  ≡⟨ cong suc (sym (+-assoc m n (m * n))) ⟩
    suc (m + n + (m * n))
  ≡⟨ cong suc (cong (_+ (m * n)) (+-comm m n)) ⟩
    suc (n + m + (m * n))
  ≡⟨ cong suc (+-assoc n m (m * n)) ⟩
    suc (n + (m + (m * n)))
  ≡⟨⟩
    suc n + (m + (m * n))
  ≡⟨ cong ((suc n) +_) (cong (m +_) (*-comm m n)) ⟩
    suc n + (m + (n * m))
  ≡⟨ cong ((suc n) +_) (sym (*-indʳ₁ n m)) ⟩
    suc n + (m * suc n)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero =
  begin
    (m + n) * zero
  ≡⟨ (*-mult0ʳ (m + n)) ⟩
    zero
  ≡⟨⟩
    zero + zero
  ≡⟨ cong (_+ zero) (sym (*-mult0ʳ m)) ⟩
    m * zero + zero
  ≡⟨ cong ((m * zero) +_) (sym (*-mult0ʳ n)) ⟩
    m * zero + n * zero
  ∎
*-distrib-+ m n (suc p) =
  begin
    (m + n) * (suc p)
  ≡⟨ (*-indʳ₁ p (m + n)) ⟩
    (m + n) + (p * (m + n))
  ≡⟨ cong ((m + n) +_) (*-comm p (m + n)) ⟩
    (m + n) + ((m + n) * p)
  ≡⟨⟩
    m + n + ((m + n) * p)
  ≡⟨ cong ((m + n) +_) (*-distrib-+ m n p) ⟩
    (m + n) + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc (m + n) (m * p) (n * p)) ⟩
    ((m + n) + (m * p)) + (n * p)
  ≡⟨⟩
    m + n + (m * p) + (n * p)
  ≡⟨ cong (_+ (n * p)) (+-assoc m n (m * p)) ⟩
    m + (n + (m * p)) + (n * p)
  ≡⟨ cong (_+ (n * p)) (cong (m +_) (+-comm n (m * p))) ⟩
    (m + ((m * p) + n)) + (n * p)
  ≡⟨  cong (_+ (n * p)) (sym (+-assoc m (m * p) n))  ⟩
    m + (m * p) + n + (n * p)
  ≡⟨⟩
    (m + (m * p)) + n + (n * p)
  ≡⟨ +-assoc (m + (m * p)) n (n * p) ⟩
    (m + (m * p)) + (n + (n * p))
  ≡⟨ cong (_+ (n + (n * p))) (sym (*-indʳ p m)) ⟩
    m * (suc p) + (n + (n * p))
  ≡⟨ cong ((m * (suc p)) +_) (sym (*-indʳ p n)) ⟩
    m * (suc p) + n * suc p

  ∎
