-- pragma to ensure everything defined must be total by default.
-- non-total functions must explicitly be marked partial.
%default total

-- Our expression DSL, this time definitely higher order!
data Expr : (a : Type) -> Type where
  Lit : a -> Expr a
  Lam : (a -> Expr b) -> Expr (a -> b)
  Add : Num a => Expr a -> Expr a -> Expr a
  App : Expr (a -> b) -> Expr a -> Expr b
  Map : Functor f => Expr (a -> b) -> Expr (f a) -> Expr (f b)

-- Some functions to deal with the 'Weak HOAS' approach
-- this can be seen in the Lam constructors first argument
-- (a -> Expr b). Totality can be proven on weak HOAS, but not
-- regular HOAS.

weaken : (Expr a -> Expr b) -> (a -> Expr b)
weaken = \f, x => f (Lit x)

-- A smart constructor to ensure all partially applied Expr
-- functions are weaken before being constructed through 'Lam'
lam : (Expr a -> Expr b) -> Expr (a -> b)
lam = \f => Lam (weaken f)

-- Our trusty evaluator
eval : Expr a -> a
eval (Lit x) = x
eval (Lam f) = \x => eval (f x)
eval (Add x y) = (eval x) + (eval y)
eval (App f x) = (eval f) (eval x)
eval (Map f xs) = map (eval f) (eval xs)

--Pi Types!
GoRight : Expr a -> Maybe Type
GoRight (Lit x) = Nothing
GoRight (Lam f) = Nothing
GoRight (Add {a} x y) = Just a
GoRight (App {a} f x) = Just a
GoRight (Map {f}{a} f' xs) = Just (f a)

GoLeft : Expr a -> Maybe Type
GoLeft (Lit x) = Nothing
GoLeft (Lam f) = Nothing
GoLeft (Add {a} x y) = Just a
GoLeft (App {a}{b} f x) = Just (a -> b)
GoLeft (Map {a}{b} f xs) = Just (a -> b)

-- Context
data Context : Maybe Type -> Type where
  Root : Context (Just a)
  L    : (x : Expr a) -> Context (Just a) -> Context (GoLeft x)
  R    : (x : Expr a) -> Context (Just a) -> Context (GoRight x)

-- Zipper
data Zipper : (a : Type) -> Type where
  Zip : Expr a -> Context (Just a) -> Zipper a

wrap : Zipper a -> Maybe (a : Type ** Zipper a)
wrap z = Just (_ ** z)

unwrap : (x : Maybe (a : Type ** Zipper a))
  -> {auto prf : IsJust x}
  -> (a : Type ** Zipper a)
unwrap (Just s) = s

-- direction functions
left : Maybe (a : Type ** Zipper a) -> Maybe (a : Type ** Zipper a)
left Nothing = Nothing
left (Just (x ** pf)) =
  case pf of
    (Zip (Lit x) c) => Nothing
    (Zip (Lam f) c) => Nothing
    (Zip p@(Add x y) c) => Just (_ ** Zip x (L p c))
    (Zip p@(App f x) c) => Just (_ ** Zip f (L p c))
    (Zip p@(Map f xs) c) => Just (_ ** Zip f (L p c))

right : Maybe (a : Type ** Zipper a) -> Maybe (a : Type ** Zipper a)
right Nothing = Nothing
right (Just (x ** pf)) =
  case pf of
    (Zip (Lit x) c) => Nothing
    (Zip (Lam f) c) => Nothing
    (Zip p@(Add x y) c) => Just (_ ** Zip y (R p c))
    (Zip p@(App f x) c) => Just (_ ** Zip x (R p c))
    (Zip p@(Map f xs) c) => Just (_ ** Zip xs (R p c))

up : Maybe (a : Type ** Zipper a) -> Maybe (a : Type ** Zipper a)
up Nothing = Nothing
up (Just (x ** pf)) = 
  case pf of
    (Zip e Root) => Nothing
    (Zip e (R (Lit x) pc)) impossible
    (Zip e (R (Lam f) pc)) impossible
    (Zip e (R (Add x y) pc)) => Just (_ ** Zip (Add x e) pc)
    (Zip e (R (App f x) pc)) => Just (_ ** Zip (App f e) pc)    
    (Zip e (R (Map f xs) pc)) => Just (_ ** Zip (Map f e) pc)
    (Zip e (L (Lit x) pc)) impossible
    (Zip e (L (Lam f) pc)) impossible
    (Zip e (L (Add x y) pc)) => Just (_ ** Zip (Add e x) pc)
    (Zip e (L (App f x) pc)) => Just (_ ** Zip (App e x) pc)
    (Zip e (L (Map f xs) pc)) => Just (_ ** Zip (Map e xs) pc)

subst : (x : (a : Type ** Zipper a)) -> Expr (fst x) 
  -> (b : Type ** Zipper b)
subst (x ** (Zip e c)) e' = (_ ** Zip e' c)

interp : (x : (a : Type ** Zipper a)) -> (fst x)
interp (x ** (Zip e c)) = eval e

-- lets try it

ex1 : Num a => Expr (List a)
ex1 = Map (lam (Add (Lit 2))) (Lit [1, 2, 3])

ex2 : Maybe (a : Type ** Zipper a)
ex2 = Just (_ ** Zip ex1 Root)

ex3 : Maybe (a : Type ** Zipper a)
ex3 = left ex2

ex4 : (a : Type ** Zipper a)
ex4 = unwrap $ up $ Just $ subst (unwrap ex3) (lam (Add (Lit 10)))

ex5 : (DPair.fst Main.ex4)
ex5 = interp ex4
-- results in [11, 12, 13]





    




