{-# OPTIONS -W noUnreachableClauses #-}

module PFPL.Chapter2 where



-- # 2.1 Judgments

data Type : Set where
  nat : Type
  tree : Type
  list : Type

-- # 2.2 Inference Rules

data Term : Set where
  zero : Term
  succ : Term → Term
  empty : Term
  node : Term → Term → Term
  nil : Term
  cons : Term → Term → Term

  -- # 2.7 Modes
  _+_ : Term → Term → Term


infix 0 _∷_
data _∷_ : Term → Type → Set where
  zero-nat : zero ∷ nat
  succ-nat : ∀ {a} → a ∷ nat → succ a ∷ nat
  empty-tree : empty ∷ tree
  node-tree : ∀ {a b} → a ∷ tree → b ∷ tree → node a b ∷ tree
  nil-list : nil ∷ list
  cons-list : ∀ {a b} → a ∷ nat → b ∷ list → cons a b ∷ list


-- _=_ in the book
infix 0 _is_
data _is_ : Term → Term → Set where
  zero-is : zero is zero
  succ-is : ∀ {a b} → a is b → succ a is succ b
  empty-is : empty is empty
  node-is : ∀ {a a' b b'} → a is a' → b is b' → node a b is node a' b'
  nil-is : nil is nil
  cons-is : ∀ {a a' b b'} → a is a' → b is b' → cons a b is cons a' b'

  -- # 2.7 Modes
  +-zero-is : ∀ {a} → a ∷ nat → a + zero is a
  +-succ-is : ∀ {a b c} → a + b is c → a + succ b is succ c



-- 2.4 # Rule Induction

nat-induction : ∀ {a} {P : Term → Set} → P zero → (∀ {x} → (x ∷ nat) → P x → P (succ x)) → (a ∷ nat) → P a
nat-induction pz ps zero-nat = pz
nat-induction pz ps (succ-nat jdg) = ps jdg (nat-induction pz ps jdg)

tree-induction : ∀ {a} {P : Term → Set} → (a ∷ tree) → P empty → (∀ {a₁ a₂} → (a₁ ∷ tree) → (a₂ ∷ tree) → P a₁ → P a₂ → P (node a₁ a₂)) → P a
tree-induction empty-tree pe pn = pe
tree-induction (node-tree jdg₁ jdg₂) pe pn = pn jdg₁ jdg₂ (tree-induction jdg₁ pe pn) (tree-induction jdg₂ pe pn)

succ-a⇒a : ∀ {a} → succ a ∷ nat → a ∷ nat
succ-a⇒a (succ-nat a) = a
-- -- can we implement it via `nat-induction`?
-- succ-a⇒a a = nat-induction a ? λ a' jdg → a'

nat-is : ∀ {a} → a ∷ nat → a is a
nat-is zero-nat = zero-is
nat-is (succ-nat ty) = succ-is (nat-is ty)
nat-is = nat-induction {P = λ x → x is x} zero-is λ _ jdg → succ-is jdg

suc-a⇒a-is-a : ∀ {a₁ a₂} → succ a₁ is succ a₂ → a₁ is a₂
suc-a⇒a-is-a (succ-is proof) = proof


-- # 2.5 Iterated and Simultaneous Inductive Definitions

data _even : Term → Set
data _odd : Term → Set

data _even where
  zero-even : zero even
  succ-even : ∀ {a} → a odd → succ a even

data _odd where
  succ-odd : ∀ {a} → a even → succ a odd

even-nat : ∀ {a} → a even → a ∷ nat
even-nat zero-even = zero-nat
even-nat (succ-even (succ-odd x)) = succ-nat (succ-nat (even-nat x))

odd-nat : ∀ {a} → a odd → a ∷ nat
odd-nat (succ-odd x) = succ-nat (even-nat x)


-- # 2.6 Defining Functions by Rules

data sum : Term → Term → Term → Set where
  sum-zero : {b : Term} → (b ∷ nat) → sum zero b b
  sum-succ : ∀ {a b c} → sum a b c → sum (succ a) b (succ c)

open import Data.Product

exists-sum : ∀ {a b} → (a ∷ nat) → (b ∷ nat) → Σ Term (sum a b)
exists-sum {b = b} zero-nat bnat = b , sum-zero bnat
exists-sum {a = a} {b} (succ-nat anat) bnat with exists-sum anat bnat
... | c , cproof = succ c , sum-succ cproof 

unique-sum : ∀ {a b c c'} → sum a b c → sum a b c' → c is c'
unique-sum (sum-zero c) (sum-zero _) = nat-is c
unique-sum (sum-succ s1) (sum-succ s2) = succ-is (unique-sum s1 s2)

