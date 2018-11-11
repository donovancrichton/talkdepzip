%default total
-- %hide Prelude.Nat.Nat
-- data Nat = Z | S Nat

data Test a = T Int | B Bool | C a

data Vec : (n : Nat) -> (e : Type) -> Type where
  Nil : Vec Z e
  (::) : (x : e) -> (xs : Vec n e) -> Vec (S n) e

(+) : Num a => Vec n a -> Vec n a -> Vec n a
(+) [] [] = []
(+) (x :: xs) (y :: ys) = x + y :: xs + ys

len1 : {a : Type} -> {n : Nat} -> Vec n a -> Nat
len1 xs {n} = n

Age : Type
Age = Nat

Name : Type
Name = String

data Material = Plastic | Wood | Metal | Cheese
data Person = P Name Age
data Object = O Material

-- A pi type to distinguish between person and object
IsPerson : Bool -> Type
IsPerson True = Person
IsPerson False = Object

-- A function that calculates the correct return type.
isPerson : (x : Bool) -> IsPerson x
isPerson True = Main.P "Donovan Crichton" 33
isPerson False = O Cheese

f : (x : Bool ** IsPerson x)
f = (_ ** isPerson True)
  
g : Num a => (n : Nat ** Vec n a)
g = (_ ** [1, 2, 3])

len : Num a => Vec n a -> (n : Nat ** Vec n a)
len x = (_ ** x)

data Expr : Type -> Type where
  Lit   : a -> Expr a
  Add   : Num a => Expr a -> Expr a -> Expr a
  Const : Expr a -> Expr b -> Expr a

interp : Expr a -> a
interp (Lit x)     = x
interp (Add x y)   = (interp x) + (interp y)
interp (Const x y) = const (interp x) (interp y)

data Context = Root
  | L (Expr a) Context 
  | R (Expr a) Context

left : (Expr a, Context) -> (Expr a, Context)
left (Lit x, c) = (Lit x, c)
left (Add x y, c) = (x, L (Add x y) c)
left (Const x y, c) = (x, L (Const x y) c)


