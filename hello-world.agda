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



