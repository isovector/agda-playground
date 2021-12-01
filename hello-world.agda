import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; cong; sym; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = 7

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (suc zero) + suc (suc (suc zero))
  ≡⟨⟩
    suc ((suc zero) + suc (suc (suc zero)))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc m * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ = refl

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ suc n = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

infixl 6 _+_ 
infixl 7 _*_


data Bin : Set where
  ! : Bin
  _O : Bin → Bin
  _I : Bin → Bin

elevenB : Bin
elevenB = ! I O I I

inc : Bin → Bin
inc ! = ! I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc (! O) ≡ ! I
_ = refl

_ : inc (! I) ≡ ! I O
_ = refl

_ : inc (! I O) ≡ ! I I
_ = refl

_ : inc (! I I) ≡ ! I O O
_ = refl

to : ℕ → Bin
to zero = ! O
to (suc x) = inc (to x)

from : Bin → ℕ
from ! = zero
from (x O) = from x * 2
from (x I) = from x * 2 + 1

-- _ : (x : ℕ) → 3 ≡ from (to 3)
-- _ = λ x → refl

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
    suc (m + n + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎


identityʳ : ∀ (m : ℕ) → m + zero ≡ m
identityʳ zero = refl
identityʳ (suc z) =
    begin
      suc z + zero
    ≡⟨⟩
      suc (z + zero)
    ≡⟨ cong suc (identityʳ z) ⟩
      suc z
    ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
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
     
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
      m + zero
    ≡⟨ identityʳ m ⟩
      m
    ≡⟨⟩
      zero + m
    ∎
+-comm m (suc n) =
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
      (m + n) + (p + q)
    ≡⟨ (+-assoc m n (p + q)) ⟩
      m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
        m + (n + p + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
        (m + (n + p)) + q
    ∎


+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                        = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl


+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

*-identity' : ∀ (n : ℕ) → n * 1 ≡ n
*-identity' zero = refl
*-identity' (suc n) rewrite *-identity' n = refl

*-ann : ∀ (n : ℕ) → n * 0 ≡ 0
*-ann zero = refl
*-ann (suc n) rewrite *-ann n = refl


+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

*-suc' : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc' zero n    = refl
*-suc' (suc m) n
  rewrite *-suc' m n
         | sym (+-assoc' m n (m * n))
         | sym (+-assoc' n m (m * n))
         | +-comm n m 
         = refl


+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero    rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl


*-comm' : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm' m zero    rewrite *-identity' m | *-ann m = refl
*-comm' m (suc n) rewrite *-suc' m n | *-comm' m n = refl

swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
swap m n p
  rewrite sym (+-assoc m n p)
        | +-comm m n
        | +-assoc n m p
        = refl

suc-+-suc : ∀ (m n : ℕ) → suc m + n ≡ m + suc n
suc-+-suc zero n = refl
suc-+-suc (suc m) n =
  begin
      suc (suc m) + n
    ≡⟨ cong suc (suc-+-suc m n) ⟩
      suc m + suc n
    ∎


*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
        | +-assoc p (m * p) (n * p)
        = refl


*-assoc' : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc' zero    n p = refl
*-assoc' (suc m) n p
  rewrite *-assoc' m n p
        | *-distrib-+ n (m * n) p
        | *-assoc' m n p
        = refl



    

-- *-distrib-+ m n zero
--   rewrite *-ann (m + n)
--         | *-ann m
--         | *-ann n
--         = refl
-- *-distrib-+ m n (suc p) = {!!}
