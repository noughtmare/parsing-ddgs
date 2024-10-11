{-# LANGUAGE GHC2021, GADTs, DataKinds, LambdaCase #-}

import Data.Char (intToDigit)

-- PARSING

data Var ctx a where
  Here :: Var (a : ctx) a
  There :: Var ctx a -> Var (b : ctx) a

type Fun a b = a -> [b]

data CFG ctx a where
  Fail :: CFG ctx a
  Or   :: CFG ctx a -> CFG ctx a -> CFG ctx a
  Done :: a -> CFG ctx a
  Seq  :: CFG ctx a -> (a -> CFG ctx b) -> CFG ctx b
  Char :: Char -> CFG ctx ()
  Var  :: Var ctx (Fun x a) -> x -> CFG ctx a
  Fix  :: (x -> CFG (Fun x a : ctx) a) -> x -> CFG ctx a

nullable :: (forall x. Var ctx x -> x) -> CFG ctx a -> [a]
nullable _ Fail = []
nullable ev (Or p q) = nullable ev p ++ nullable ev q
nullable _ (Done x) = [x]
nullable ev (Seq p q) = 
  [ y | x <- nullable ev p, y <- nullable ev (q x) ]
nullable _ (Char _) = []
nullable ev (Var v x) = ev v x
nullable ev (Fix p x) = nullable (\case Here -> const []; There v -> ev v) (p x)

subst :: (forall x y. Var ctx (Fun x y) -> x -> CFG ctx' y) -> CFG ctx a -> CFG ctx' a
subst _ Fail = Fail
subst f (Or x y) = Or (subst f x) (subst f y)
subst _ (Done x) = Done x
subst f (Seq x y) = Seq (subst f x) (subst f . y)
subst _ (Char c) = Char c
subst f (Var v x) = f v x
subst f (Fix p x) = Fix (subst (\case Here -> Var Here; There v -> wk There . f v) . p) x

wk :: (forall x. Var ctx x -> Var ctx' x) -> CFG ctx a -> CFG ctx' a
wk f = subst (Var . f)

derivative :: CFG ctx a -> (forall x. Var ctx x -> (x, Var ctx x))
           -> Char -> CFG ctx a
derivative Fail _ _ = Fail
derivative (Or p q) ev c = Or (derivative p ev c) (derivative q ev c)
derivative (Done _) _ _ = Fail
derivative (Seq p q) ev c = Or (Seq (derivative p ev c) q)
  (foldr Or Fail [derivative (q x) ev c | x <- nullable (fst . ev) p])
derivative (Char c') _ c = if c == c' then Done () else Fail
derivative (Var v x) ev _ = Var (snd (ev v)) x
derivative (Fix p x) ev c =
  subst
    (\case
      Here -> Fix p
      There v -> Var v)
    (Fix
      (\x -> derivative
        (wk There (p x))
        (\case
          Here -> error "impossible"
          There Here -> (nullable (fst . ev) . Fix p, Here)
          There (There v) -> fmap (There . There) (ev v))
        c)
      x)

parse :: CFG '[] a -> String -> [a]
parse s [] = nullable (\case) s
parse s (x:xs) = parse (derivative s (\case) x) xs

digit = foldr Or Fail [Seq (Char (intToDigit x)) (\() -> Done x) | x <- [0..9]]

guard False = Fail
guard True = Done ()

ndots = Seq digit (Fix (\i -> Or 
  (Seq (guard (i > 0)) (\() -> Seq (Char '.') (\() -> Var Here (i - 1))))
  (guard (i == 0))
  ))

-- >>> parse ndots "5....."
-- [()]

ndotsl :: Int -> CFG ctx ()
ndotsl = Fix (\i -> Or 
  (Seq (guard (i > 0)) (\() -> Seq (Var Here (i - 1)) (\() -> Char '.')))
  (guard (i == 0))
  )

ndotsl' :: Int -> CFG ctx ()
ndotsl' = Fix (\i -> Seq (guard (i > 0)) (\() -> Or 
  (Seq (Var Here (i - 1)) (\() -> Char '.'))
  (guard (i == 1))
  ))

data X = A Int | Add X X deriving Show

ex = Fix 
  (\i -> Or 
    (Seq digit (Done . A))
    (Seq (guard i) (\() -> Seq (Var Here False) (\x -> Seq (Char '+') (\() -> Seq (Var Here True) (Done . Add x))))))
  True

-- >>> parse ex "1+2+3"
-- [Add (A 1) (Add (A 2) (A 3))]
