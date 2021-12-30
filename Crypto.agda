{-# OPTIONS --type-in-type #-}

module Crypto where

open import Prelude
open import Algebra.Bundles using (CommutativeRing)

infix 3 _==_mod_
record _==_mod_ (a b n : Nat) : Set where
  constructor mod-cong
  field
    p : Nat
    q : Nat
    r : Nat
    a-proof : a == p * n + r
    b-proof : b == q * n + r

ex : 38 == 14 mod 12
ex = mod-cong 3 1 2 refl refl

record Field (N : Set) : Set where
  constructor mk-field
  infixr 6 _*f_
  infixr 5 _+f_
  infixr 0 _~~_

  field
    _~~_ : N -> N -> Set
    f-zero : N
    f-one : N
    negate : N -> N
    recip : (n : Σ N (_=/= f-zero)) -> N
    _+f_ : N -> N -> N
    _*f_ : N -> N -> N

    negate-inverse : (n : N) -> n +f negate n ~~ f-zero
    negate-negate : (n : N) -> negate (negate n) ~~ n
    recip-inverse : (n : Σ N (_=/= f-zero)) -> Σ.fst n *f recip n ~~ f-one
    recip-not-zero : (n : Σ N (_=/= f-zero)) -> recip n =/= f-zero
    recip-recip : (n : Σ N (_=/= f-zero)) -> recip (recip n , recip-not-zero n) ~~ Σ.fst n

    +f-commutes : (a b : N) -> a +f b ~~ b +f a
    *f-commutes : (a b : N) -> a +f b ~~ b +f a
    +f-assoc : (a b c : N) -> a +f (b +f c) ~~ (a +f b) +f c
    *f-assoc : (a b c : N) -> a *f (b *f c) ~~ (a *f b) *f c
    +f-*f-distrib : (a b c : N) -> a *f (b +f c) ~~ a *f b +f a *f c

open Field

to-nat : {z : Nat} -> Fin z -> Nat
to-nat fz = 0
to-nat (fs n) = suc (to-nat n)

modulo : Nat -> Nat -> Nat
modulo n k = ?

modulo<k : (n k : Nat) -> modulo n k < k
modulo<k n k = ?

f-field : {n : Nat} -> Field (Fin (2 + n))
_~~_ (f-field {n}) a b = to-nat a == to-nat b mod n
f-zero f-field = fz
f-one f-field = fs fz
negate (f-field {n}) a = to-fin (n ∸ to-nat a) ?
recip (f-field {n}) a = ?
_+f_ (f-field {n}) a b = to-fin (modulo (to-nat a + to-nat b) (2 + n)) (modulo<k (to-nat a + to-nat b) (2 + n))
_*f_ (f-field {n}) a b = to-fin (modulo (to-nat a * to-nat b) (2 + n)) (modulo<k (to-nat a * to-nat b) (2 + n))
negate-inverse f-field = ?
negate-negate f-field = ?
recip-inverse f-field = ?
recip-not-zero f-field = ?
recip-recip f-field = ?
+f-commutes f-field = ?
*f-commutes f-field = ?
+f-assoc f-field = ?
*f-assoc f-field = ?
+f-*f-distrib f-field = ?

record AbelianGroup : Set where
  constructor mk-abelian-group
  infixr 6 _+g_

  field
    GElem : Set
    g-zero : GElem
    negate : GElem -> GElem
    _+g_ : GElem -> GElem -> GElem

    negate-inverse : (n : GElem) -> n +g negate n == g-zero
    negate-negate : (n : GElem) -> negate (negate n) == n

    +g-commutes : (a b : GElem) -> a +g b == b +g a
    +g-assoc : (a b c : GElem) -> a +g (b +g c) == (a +g b) +g c

open AbelianGroup

_*g_ : (g : AbelianGroup) -> Nat -> GElem g -> GElem g
(group *g zero) n = g-zero group
(group *g suc q) n = _+g_ group n (_*g_ group q n)

E : Nat -> AbelianGroup
E = ?

data IsPrime : Nat -> Set

record Generator (q : Nat) : Set where
  constructor mk-generator
  field
    group : AbelianGroup
    generator : GElem group
    q-is-prime : IsPrime q
    proof : _*g_ group q generator == g-zero group

open Generator

SecretKey : Nat -> Set
SecretKey = Fin

record PublicKey (q : Nat) : Set where
  field
    gen : Generator q
    secret-key : SecretKey q
    public-key : GElem (group gen)
    proof-public-key : _*g_ (group gen) (to-nat secret-key) (generator gen) == public-key

-- point hash
Hp : (G : AbelianGroup) -> GElem G -> GElem G
Hp = ?


data String : Set

Hs : {q : Nat} -> (G : AbelianGroup) -> String -> GElem G -> GElem G -> Fin q
Hs = ?




