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
isPerson True = P "Donovan Crichton" 33
isPerson False = O Cheese
  
