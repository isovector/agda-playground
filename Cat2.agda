{-# OPTIONS --type-in-type #-}

module Cat2 where

open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_; [_] to [[_]])
open import Tactic.Rewrite using (cong!)

infix 3 _done
infixr 2 _=[]_ step-=
infix 1 begin_

begin_ : {A : Set} -> A -> A
begin_ x = x

_=[]_ : {A : Set} (x : A) -> {y : A} -> x == y -> x == y
_=[]_ _ x = x

step-= : {A : Set} (x : A) -> {y z : A} -> y == z -> x == y -> x == z
step-= _ yz xy = trans xy yz

syntax step-= x yz xy = x =[ xy ] yz

_done : {A : Set} -> (x : A) -> x == x
_done _ = refl




postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g



record Category : Set where
  infix 6 _~>_
  field
    Obj : Set
    _~>_ : (A B : Obj) → Set

    id : {A : Obj} → A ~> A
    _>>_ : {A B C : Obj} → A ~> B → B ~> C → A ~> C

    id-l : {A B : Obj} (f : A ~> B) → id >> f == f
    id-r : {A B : Obj} (f : A ~> B) → f >> id == f
    >>-assoc : {A B C D : Obj} (f : A ~> B) → (g : B ~> C) → (h : C ~> D) → f >> (g >> h) == (f >> g) >> h


infix 5 _[_,_]
_[_,_] : (C : Category) -> Category.Obj C -> Category.Obj C -> Set
C [ X , Y ] = Category._~>_ C X Y

infix 5 _[_>>_]
_[_>>_] : (C : Category) -> {X Y Z : Category.Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
C [ f >> g ] = Category._>>_ C f g


SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \ S T → S → T
        ; id = \ x → x
        ; _>>_ = λ f g x →  g (f x)
        ; id-l = \f -> refl
        ; id-r = \f -> refl
        ; >>-assoc = \f g h -> refl
        }


module FUNCTOR where
    open Category

    infix 6 _=>_
    record _=>_ (C : Category) (D : Category) : Set where
      field
        F-Obj : Obj C → Obj D
        F-map : {A B : Obj C} → C [ A , B ] → D [ F-Obj A , F-Obj B ]

        F-map-id : (A : Obj C) → F-map (id C {A}) == id D {F-Obj A}
        F-map->> : {X Y Z : Obj C} (f : C [ X ,  Y ]) → (g : C [ Y ,  Z ]) → (F-map ( C [ f >> g ])) == (D [ F-map f >> F-map g ])



open FUNCTOR

ID=> : {C : Category} → C => C
ID=> = record
     { F-Obj = λ x → x
     ; F-map = λ x → x
     ; F-map-id = \a → refl
     ; F-map->> = \f g -> refl
     }

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

MAYBE : SET => SET
MAYBE = record
  { F-Obj = Maybe
  ; F-map = λ { f (just x) → just (f x) ; f nothing → nothing }
  ; F-map-id = \a -> extensionality λ { (just x) → refl ; nothing → refl }
  ; F-map->> = \f g -> extensionality λ { (just x) → refl ; nothing → refl }
  }

infixr 10 _,-_
data List (A : Set) : Set where
  [] : List A
  _,-_ : A → List A → List A

list : {A B : Set} → (A → B) → List A → List B
list f [] = []
list f (x ,- xs) = f x ,- list f xs

LIST : SET => SET
LIST = record
  { F-Obj = List
  ; F-map =  list
  ; F-map-id = \a -> extensionality help
  ; F-map->> = \f g -> extensionality λ { x → yelp f g x }
  }
  where
    help : {A : Set} (x : List A) → list (λ x → x) x == x
    help [] = refl
    help (x ,- xs) rewrite help xs = refl

    yelp : ∀ {X} {Y} {Z} (f : SET [ X , Y ]) (g : SET [ Y , Z ])
         (x : List X) → list (SET [ f >> g ]) x == (SET [ list f >> list g ]) x
    yelp f g [] = refl
    yelp f g (x ,- xs) rewrite yelp f g xs = refl



module NAT-TRANS where
  open Category
  open _=>_
  record _~~>_ {C D : Category} (F G : C => D) : Set where
    field
        hoist : (X : Obj C) →  D [ F-Obj F X , F-Obj G X ]
        nat : {X Y : Obj C} {f : C [ X , Y ]} →  D [ hoist X >> F-map G f ] == D [ F-map F f >> hoist Y ]

open NAT-TRANS

LIST-TO-MAYBE : LIST ~~> MAYBE
LIST-TO-MAYBE = record
  { hoist = λ { X [] → nothing ; X (x ,- _) → just x }
  ; nat = extensionality λ { [] → refl ; (x ,- x₁) → refl }
  }

infix 4 _,_,_
record Sg2 (A B : Set) (C : A -> B -> Set) : Set where
  constructor _,_,_
  field
    fst : A
    snd : B
    sg2 : C fst snd

uip : {A : Set} -> {x y : A} -> (p q : x == y) -> p == q
uip refl refl = refl

module COMMA {A B C : Category} (S : A => C) (T : B => C) where
  open Category
  open _=>_

  record CommaObj : Set where
    constructor comma-obj
    field
      {alpha} : Obj A
      {beta}  : Obj B
      hom : C [ F-Obj S alpha , F-Obj T beta ]

  open CommaObj

  record CommaArr (X Y : CommaObj) : Set where
    constructor comma-hom
    field
      f : A [ X .alpha , Y .alpha ]
      g : B [ X .beta , Y .beta ]
      commute : C [ F-map S f >> Y .hom ] == C [ X .hom >> F-map T g ]

  open CommaArr

  comma-ext
      : {X Y : CommaObj}
     -> (tau psi : CommaArr X Y)
     -> tau .f == psi .f
     -> tau .g == psi .g
     -> tau == psi
  comma-ext (comma-hom _ _ h1) (comma-hom _ _ h2) f-eq g-eq
    rewrite f-eq | g-eq | uip h1 h2
      = refl

  Comma : Category
  Category.Obj Comma = CommaObj
  Category._~>_ Comma = CommaArr

  Category.id Comma {A = comma-obj {a} {b} h}
    = comma-hom
        (id A)
        (id B)
        ( begin
          C [ F-map S (id A {a}) >> h ]  =[ cong! (F-map-id S a) ]
          C [ id C {F-Obj S a} >> h ]    =[ cong! (id-l C h) ]
          h                              =[ cong! (sym (id-r C h)) ]
          C [ h >> id C {F-Obj T b} ]    =[ cong! (sym (F-map-id T b)) ]
          C [ h >> F-map T (id B {b}) ]
          done
        )

  Category._>>_ Comma {A = comma-obj {a1} {b1} tau}
                      {B = comma-obj {a2} {b2} psi}
                      {C = comma-obj {a3} {b3} phi}
                      (comma-hom f  g h)
                      (comma-hom f' g' h')
    = comma-hom
        (A [ f >> f' ])
        (B [ g >> g' ])
        ( begin
          C [ F-map S (A [ f >> f' ]) >> phi ]        =[ cong! (F-map->> S f f') ]
          C [ C [ F-map S f >> F-map S f' ] >> phi ]  =[ sym (>>-assoc C (F-map S f) (F-map S f') phi) ]
          C [ F-map S f >> C [ F-map S f' >> phi ] ]  =[ cong (\x -> C [ F-map S f >> x ] ) h' ]
          C [ F-map S f >> C [ psi >> F-map T g' ] ]  =[ >>-assoc C (F-map S f) psi (F-map T g') ]
          C [ C [ F-map S f >> psi ] >> F-map T g' ]  =[ cong (\x -> C [ x >> F-map T g' ] ) h ]
          C [ C [ tau >> F-map T g ] >> F-map T g' ]  =[ sym (>>-assoc C tau (F-map T g) (F-map T g')) ]
          C [ tau >> C [ F-map T g >> F-map T g' ] ]  =[ cong! (sym (F-map->> T g g')) ]
          C [ tau >> F-map T (B [ g >> g' ]) ]
          done
        )

  id-l Comma (comma-hom f g _) = comma-ext _ _ (id-l A f) (id-l B g)
  id-r Comma (comma-hom f g _) = comma-ext _ _ (id-r A f) (id-r B g)

  >>-assoc Comma (comma-hom a-f b-f _)
                 (comma-hom a-g b-g _)
                 (comma-hom a-h b-h _)
    = comma-ext _ _ (>>-assoc A a-f a-g a-h) (>>-assoc B b-f b-g b-h)

