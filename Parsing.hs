{-# LANGUAGE GHC2021, GADTs, DataKinds, LambdaCase #-}

-- PARSING

data Var ctx a where
  Here :: Var (a : ctx) a
  There :: Var ctx a -> Var (b : ctx) a

data CFG ctx a where
  Fail :: CFG ctx a
  Or   :: CFG ctx a -> CFG ctx a -> CFG ctx a
  Done :: a -> CFG ctx a
  Seq  :: CFG ctx a -> (a -> CFG ctx b) -> CFG ctx b
  Char :: Char -> CFG ctx ()
  Var  :: Var ctx [a] -> CFG ctx a
  Fix  :: CFG ([a] : ctx) a -> CFG ctx a

nullable :: (forall x. Var ctx x -> x) -> CFG ctx a -> [a]
nullable _ Fail = []
nullable ev (Or p q) = nullable ev p ++ nullable ev q
nullable _ (Done x) = [x]
nullable ev (Seq p q) = 
  [ y | x <- nullable ev p, y <- nullable ev (q x) ]
nullable _ (Char _) = []
nullable ev (Var v) = ev v
nullable ev (Fix p) = nullable (\case Here -> []; There v -> ev v) p

subst :: (forall x. Var ctx [x] -> CFG ctx' x) -> CFG ctx a -> CFG ctx' a
subst _ Fail = Fail
subst f (Or x y) = Or (subst f x) (subst f y)
subst _ (Done x) = Done x
subst f (Seq x y) = Seq (subst f x) (subst f . y)
subst _ (Char c) = Char c
subst f (Var v) = f v
subst f (Fix x) = Fix (subst (\case Here -> Var Here; There v -> wk There (f v)) x)

wk :: (forall x. Var ctx x -> Var ctx' x) -> CFG ctx a -> CFG ctx' a
wk f = subst (Var . f)

ap :: CFG ([x] : ctx) a -> CFG ctx x -> CFG ctx a
ap x y = subst (\case Here -> y ; There v -> Var v) x

derivative :: CFG ctx a -> (forall x. Var ctx x -> (x, Var ctx x)) -> Char -> CFG ctx a
derivative Fail _ _ = Fail
derivative (Or p q) ev c = Or (derivative p ev c) (derivative q ev c)
derivative (Done _) _ _ = Fail
derivative (Seq p q) ev c = Or (Seq (derivative p ev c) q)
  (foldr Or Fail [derivative (q x) ev c | x <- nullable (fst . ev) p])
derivative (Char c') _ c = if c == c' then Done () else Fail
derivative (Var v) ev _ = Var (snd (ev v))
derivative (Fix p) ev c =
  ap
    (Fix
      (derivative
        (wk There p)
        (\case
          Here -> error "impossible"
          There Here -> (nullable (fst . ev) (Fix p), Here)
          There (There v) -> fmap (There . There) (ev v))
        c))
    (Fix p)

parse :: CFG '[] a -> String -> [a]
parse s [] = nullable (\case) s
parse s (x:xs) = parse (derivative s (\case) x) xs

data Bin = BL | BN Bin Bin deriving Show

ex :: CFG ctx Bin
ex = Fix (Or
  (Seq (Char 'x') (\() -> Done BL))
  (Seq (Var Here) (\x -> Seq (Var Here) (Done . BN x))))

data Tri = TL | TN Tri Tri Tri deriving Show

ex2 :: CFG ctx Tri
ex2 = Fix (Or
  (Seq (Char 'x') (\() -> Done TL))
  (Seq (Var Here) (\x -> Seq (Var Here) (\y -> Seq (Var Here) (Done . TN x y)))))

ex3 :: CFG ctx Int
ex3 = Fix (Or (Done 1) (Seq (Var Here) (\x -> Done (x + 1))))