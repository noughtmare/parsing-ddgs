{-# LANGUAGE GHC2021, GADTs, DataKinds, LambdaCase #-}

-- RECOGNIZING

data Nat = Z | S Nat

data Var n where
  Here :: Var (S n)
  There :: Var n -> Var (S n)

data CFG n where
  Fail :: CFG n
  Or   :: CFG n -> CFG n -> CFG n
  Done :: CFG n
  Seq  :: CFG n -> CFG n -> CFG n
  Char :: Char -> CFG n
  Var  :: Var n -> CFG n
  Fix  :: CFG (S n) -> CFG n

nullable :: (Var n -> Bool) -> CFG n -> Bool
nullable _ Fail = False
nullable ev (Or p q) = nullable ev p || nullable ev q
nullable _ Done = True
nullable ev (Seq p q) = nullable ev p && nullable ev q
nullable _ (Char _) = False
nullable ev (Var v) = ev v
nullable ev (Fix p) = nullable (\case Here -> False; There v -> ev v) p

subst :: (Var n -> CFG m) -> CFG n -> CFG m
subst _ Fail = Fail
subst f (Or x y) = Or (subst f x) (subst f y)
subst _ Done = Done
subst f (Seq x y) = Seq (subst f x) (subst f y)
subst _ (Char c) = Char c
subst f (Var v) = f v
subst f (Fix x) = Fix (subst (\case Here -> Var Here; There v -> wk There (f v)) x)

wk :: (Var n -> Var m) -> CFG n -> CFG m
wk f = subst (Var . f)

derivative :: CFG n -> (Var n -> (Bool, Var n)) -> Char -> CFG n
derivative Fail _ _ = Fail
derivative (Or p q) ev c = Or (derivative p ev c) (derivative q ev c)
derivative Done _ _ = Fail
derivative (Seq p q) ev c = Or (Seq (derivative p ev c) q)
  (if nullable (fst . ev) p then derivative q ev c else Fail)
derivative (Char c') _ c = if c == c' then Done else Fail
derivative (Var v) ev _ = Var (snd (ev v))
derivative cfg@(Fix p) ev c =
  subst
    (\case
      Here -> cfg
      There v -> Var v)
    (Fix
      (derivative
        (wk There p)
        (\case
          Here -> error "impossible"
          There Here -> (nullable (fst . ev) cfg, Here)
          There (There v) -> fmap (There . There) (ev v))
        c))

recognize :: CFG Z -> String -> Bool
recognize s [] = nullable (\case) s
recognize s (x:xs) = recognize (derivative s (\case) x) xs

ex :: CFG n
ex = Fix (Or Done (Seq (Var Here) (Char 'x')))