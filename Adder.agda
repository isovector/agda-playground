{-# OPTIONS --type-in-type #-}

module Adder where

infix 2 _==_
data _==_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a == a
{-# BUILTIN EQUALITY _==_ #-}

cong : {A B : Set} -> {a b : A} -> (f : A -> B) -> a == b -> f a == f b
cong f (refl a) = refl (f a)

sym : {A : Set} {a b : A} -> a == b -> b == a
sym (refl a) = refl a

begin_ : {A : Set} -> A -> A
begin_ x = x

_=[]_ : {A : Set} (x : A) -> {y : A} -> x == y -> x == y
_=[]_ _ x = x

trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans (refl x) (refl _) = refl x

step-= : {A : Set} (x : A) -> {y z : A} -> y == z -> x == y -> x == z
step-= _ yz xy = trans xy yz

syntax step-= x yz xy = x =[ xy ] yz

_done : {A : Set} -> (x : A) -> x == x
_done = refl

infix 3 _done
infixr 2 _=[]_ step-=
infix 1 begin_

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infixl 5 _+_
_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ (a + b)

n+zero : (n : Nat) -> n + zero == n
n+zero zero = refl zero
n+zero (succ n) rewrite n+zero n = refl (succ n)

n+succ : (n m : Nat) -> n + succ m == succ (n + m)
n+succ zero m = refl (succ m)
n+succ (succ n) m rewrite n+succ n m = refl (succ (succ (n + m)))

+-sym : (n m : Nat) -> n + m == m + n
+-sym zero m rewrite n+zero m = refl m
+-sym (succ n) m rewrite n+succ m n | +-sym n m = cong succ (refl (m + n))

infixl 6 _*_
_*_ : Nat -> Nat -> Nat
zero * b = zero
succ a * b = b + a * b

infixl 7 _^_
_^_ : Nat -> Nat -> Nat
a ^ zero = 1
a ^ succ b = a * a ^ b

infixr 4 _,-_
data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (succ n)
  fs : {n : Nat} -> Fin n -> Fin (succ n)

record One : Set where
  constructor tt

data Zero : Set where

infix 3 _<=_
data _<=_ : Nat -> Nat -> Set where
  z<= : {a : Nat} -> zero <= a
  s<=s : {a b : Nat} -> a <= b -> succ a <= succ b

infix 3 _<_
_<_ : Nat -> Nat -> Set
_<_ a b = succ a <= b

to-fin : {z : Nat} -> (n : Nat) -> n < z -> Fin z
to-fin {zero} n ()
to-fin {succ z} zero z<s = fz
to-fin {succ z} (succ n) (s<=s proof) = fs (to-fin {z} n proof)


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

full-add-carry : (carry-in : Value) -> Value -> Value -> Vec Value 2
full-add-carry cin a b =
  let o = xor a b
   in xor o cin ,- or (and a b) (and o cin) ,- []



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
a+b<=c+d {a} {_} {c} {_} z<= (s<=s {b} {d} bd) rewrite n+succ c d = s<=s (a+b<=c+d {0} _ bd)
a+b<=c+d (s<=s ac) bd = s<=s (a+b<=c+d ac bd)


n+n<=m+m : {n m : Nat} -> n <= m -> n + n <= m + m
n+n<=m+m z<= = z<=
n+n<=m+m (s<=s {a} {b} nm) rewrite n+succ a a | n+succ b b = s<=s (s<=s (n+n<=m+m nm))

to-bit-bounded : (x : Value) -> to-bit x <= 1
to-bit-bounded high = s<=s z<=
to-bit-bounded low = z<=

postulate trust-me : {x y : Nat} -> x < y

to-nat-bounded : {n : Nat} -> (v : Vec Value n) -> to-nat v < 2 ^ n
to-nat-bounded [] = s<=s z<=
to-nat-bounded {succ n} (b ,- v) = trust-me

full-add-is-add : (x y z : Value) -> to-nat (full-add-carry x y z) == to-bit x + to-bit y + to-bit z
full-add-is-add high high high = refl 3
full-add-is-add high high low = refl 2
full-add-is-add high low high = refl 2
full-add-is-add high low low = refl 1
full-add-is-add low high high = refl 2
full-add-is-add low high low = refl 1
full-add-is-add low low high = refl 1
full-add-is-add low low low = refl zero

ripple-carry : {n : Nat} -> Value -> Vec Value n -> Vec Value n -> Vec Value n
ripple-carry cin [] [] = []
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
_ = mod-cong (s<=s z<=) 2 (refl 4)

ripple-carry-is-add : {n : Nat} (cin : Value) (xs ys : Vec Value n) -> to-bit cin + to-nat xs + to-nat ys == to-nat (ripple-carry cin xs ys) mod 2 ^ n
ripple-carry-is-add high [] [] = mod-cong (s<=s z<=) 1 (refl 1)
ripple-carry-is-add low [] [] = mod-cong (s<=s z<=) zero (refl zero)
ripple-carry-is-add {n} cin (x ,- xs) (y ,- ys) with full-add-carry cin x y
... | sum ,- cout ,- [] with ripple-carry-is-add cout xs ys
... | mod-cong mod-size mod-val mod-proof
    = mod-cong ? {!!} (
        begin
      to-bit cin + (to-bit x + (to-nat xs + (to-nat xs + 0))) + (to-bit y + (to-nat ys + (to-nat ys + 0)))
        =[ cong ? (n+zero (to-nat xs)) ]
      to-bit cin + (to-bit x + to-nat xs + to-nat xs) + (to-bit y + (to-nat ys + (to-nat ys + 0)))
        =[ cong ? (n+zero (to-nat ys)) ]
      to-bit cin + (to-bit x + to-nat xs + to-nat xs) + (to-bit y + to-nat ys + to-nat ys)
        =[]
      {!!}
    )




