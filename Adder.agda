{-# OPTIONS --type-in-type #-}

module Adder where

open import Data.Nat hiding (_<_)

Nat : Set
Nat = ℕ

open import Relation.Binary.PropositionalEquality


infix 2 _==_
_==_ = _≡_

begin_ : {A : Set} -> A -> A
begin_ x = x

_=[]_ : {A : Set} (x : A) -> {y : A} -> x == y -> x == y
_=[]_ _ x = x

step-= : {A : Set} (x : A) -> {y z : A} -> y == z -> x == y -> x == z
step-= _ yz xy = trans xy yz

syntax step-= x yz xy = x =[ xy ] yz

_done : {A : Set} -> (x : A) -> x == x
_done _ = refl

infix 3 _done
infixr 2 _=[]_ step-=
infix 1 begin_

n+zero : (n : Nat) -> n + zero == n
n+zero zero = refl
n+zero (suc n) rewrite n+zero n = refl

n+suc : (n m : Nat) -> n + suc m == suc (n + m)
n+suc zero m = refl
n+suc (suc n) m rewrite n+suc n m = refl

+-sym : (n m : Nat) -> n + m == m + n
+-sym zero m rewrite n+zero m = refl
+-sym (suc n) m rewrite n+suc m n | +-sym n m = cong suc refl

infixr 4 _,-_
data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

record One : Set where
  constructor tt

data Zero : Set where

infix 3 _<=_
data _<=_ : Nat -> Nat -> Set where
  z<= : {a : Nat} -> zero <= a
  s<=s : {a b : Nat} -> a <= b -> suc a <= suc b

infix 3 _<_
_<_ : Nat -> Nat -> Set
_<_ a b = suc a <= b

to-fin : {z : Nat} -> (n : Nat) -> n < z -> Fin z
to-fin {zero} n ()
to-fin {suc z} zero z<s = fz
to-fin {suc z} (suc n) (s<=s proof) = fs (to-fin {z} n proof)


lookup : {A : Set}{n : Nat} -> Vec A n -> Fin n -> A
lookup (x ,- v) fz = x
lookup (x ,- v) (fs f) = lookup v f

data Value : Set where
  high : Value
  low : Value

and : Value -> Value -> Value
and high b = b
and low b = low

or : Value -> Value -> Value
or high b = high
or low b = b

xor : Value -> Value -> Value
xor high high = low
xor high low = high
xor low high = high
xor low low = low

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B



to-bit : Value -> Nat
to-bit high = 1
to-bit low = 0

to-nat : {n : Nat} -> Vec Value n -> Nat
to-nat [] = 0
to-nat (x ,- v) = to-bit x + 2 * to-nat v

eight : Nat
eight = to-nat ( low ,- low ,- low ,- high ,- [] )

<+-trans : {a b c : Nat} -> a <= b -> b <= c -> a <= c
<+-trans z<= bc = z<=
<+-trans (s<=s ab) (s<=s bc) = s<=s (<+-trans ab bc)

a+b<=c+d : {a b c d : Nat} -> a <= c -> b <= d -> a + b <= c + d
a+b<=c+d z<= z<= = z<=
a+b<=c+d {a} {_} {c} {_} z<= (s<=s {b} {d} bd) rewrite n+suc c d = s<=s (a+b<=c+d {0} _ bd)
a+b<=c+d (s<=s ac) bd = s<=s (a+b<=c+d ac bd)


n+n<=m+m : {n m : Nat} -> n <= m -> n + n <= m + m
n+n<=m+m z<= = z<=
n+n<=m+m (s<=s {a} {b} nm) rewrite n+suc a a | n+suc b b = s<=s (s<=s (n+n<=m+m nm))

to-bit-bounded : (x : Value) -> to-bit x <= 1
to-bit-bounded high = s<=s z<=
to-bit-bounded low = z<=

postulate trust-me : {x y : Nat} -> x < y

to-nat-bounded : {n : Nat} -> (v : Vec Value n) -> to-nat v < 2 ^ n
to-nat-bounded [] = s<=s z<=
to-nat-bounded {suc n} (b ,- v) = trust-me

full-add-carry : (carry-in : Value) -> Value -> Value -> Vec Value 2
full-add-carry cin a b =
  let o = xor a b
   in xor o cin ,- or (and a b) (and o cin) ,- []

full-add-is-add : (x y z : Value) -> to-nat (full-add-carry x y z) == to-bit x + to-bit y + to-bit z
full-add-is-add high high high = refl
full-add-is-add high high low = refl
full-add-is-add high low high = refl
full-add-is-add high low low = refl
full-add-is-add low high high = refl
full-add-is-add low high low = refl
full-add-is-add low low high = refl
full-add-is-add low low low = refl

ripple-carry : {n : Nat} -> Value -> Vec Value n -> Vec Value n -> Vec Value (suc n)
ripple-carry cin [] [] = cin ,- []
ripple-carry cin (x ,- xs) (y ,- ys) with full-add-carry cin x y
... | sum ,- cout ,- [] = sum ,- ripple-carry cout xs ys

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

infix 3 _==_mod_
record _==_mod_ (m k n : Nat) : Set where
  constructor mod-cong
  field
    mod-size : k < n
    mod-val : Nat
    mod-proof : m == mod-val * n + k

_ : 4 == 0 mod 2
_ = mod-cong (s<=s z<=) 2 refl

+-assoc : (a b c : Nat) -> a + (b + c) == (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

n*zero : (n : Nat) -> n * 0 == 0
n*zero zero = refl
n*zero (suc n) = n*zero n

open import Data.Nat.Solver
open +-*-Solver

*-distrib : (a b c : Nat) -> a * (b + c) == a * b + a * c
*-distrib = solve 3 (\a b c -> a :* (b :+ c) := a :* b :+ a :* c) refl

ripple-carry-is-add : {n : Nat} (cin : Value) (xs ys : Vec Value n) -> to-bit cin + to-nat xs + to-nat ys == to-nat (ripple-carry cin xs ys)
ripple-carry-is-add cin [] [] rewrite n+zero (to-bit cin) = n+zero (to-bit cin)
ripple-carry-is-add cin (x ,- xs) (y ,- ys) = sym (
  begin
    to-nat (ripple-carry cin (x ,- xs) (y ,- ys))
  =[]
    to-nat (sum ,- ripple-carry cout xs ys)
  =[]
    to-bit sum + 2 * to-nat (ripple-carry cout xs ys)
  =[ cong (\p -> to-bit sum + 2 * p) (sym (ripple-carry-is-add cout xs ys)) ]
    to-bit sum + 2 * ((to-bit cout + to-nat xs) + to-nat ys)
  =[ {!!} ]
    to-bit sum + 2 * (to-bit cout + to-nat xs) + 2 * (to-nat ys)
  =[ {!!} ]
    to-bit sum + (2 * to-bit cout + 2 * to-nat xs) + 2 * (to-nat ys)
  =[ {!!} ]
    to-bit cin + (to-bit x + 2 * to-nat xs) + (to-bit y + 2 * to-nat ys)
  =[]
    to-bit cin + to-nat (x ,- xs) + to-nat (y ,- ys)
  done
    )
  where
    sum : Value
    sum = xor (xor x y) cin

    cout : Value
    cout = or (and x y) (and (xor x y) cin)

