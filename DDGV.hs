{- cabal:
build-depends: base, recover-rtti
-}
{-# LANGUAGE GHC2021, GADTs, DataKinds, LambdaCase, TypeFamilies #-}

{-# OPTIONS_GHC -Wall #-}

import Data.Char (intToDigit)
import Data.Kind (Type)
-- import Debug.RecoverRTTI

-- DATA-DEPENDENT PARSING WITH VARIABLES

type Var :: [Ty] -> Ty -> Type
data Var ctx a where
  HereV :: Var (V a : ctx) (V a)
  HereF :: Var (F a b : ctx) (F a b)
  There :: Var ctx a -> Var (b : ctx) a
deriving instance Show (Var ctx a)

data Ty = V Type | F Type Type

type Exp :: [Ty] -> Type -> Type
data Exp ctx a where
  ENil :: a -> Exp ctx a 
  ECons :: forall ctx a x. Var ctx (V x) -> Exp ctx (x -> a) -> Exp ctx a
deriving instance Functor (Exp ctx)

instance Applicative (Exp ctx) where
  pure = ENil
  ENil f <*> x = fmap f x
  ECons x xs <*> y = ECons x (flip <$> xs <*> y)

hereExp :: Exp (V x : ctx) x
hereExp = ECons HereV (ENil id)

thereExp :: Exp ctx a -> Exp (x : ctx) a
thereExp (ENil x) = ENil x
thereExp (ECons v x) = ECons (There v) (thereExp x)

instance Show (Exp ctx a) where
  show ENil{} = "ENil{}"
  -- show (ENil x) = "ENil (" ++ anythingToString x ++ ")"
  show (ECons v xs) = "ECons (" ++ show v ++ ") (" ++ show xs ++ ")"

type CFG :: [Ty] -> Type -> Type
data CFG ctx a where
  Fail :: CFG ctx a
  Or   :: CFG ctx a -> CFG ctx a -> CFG ctx a
  Done :: Exp ctx a -> CFG ctx a
  Seq  :: CFG ctx a -> (CFG (V a : ctx) b) -> CFG ctx b
  Char :: Char -> CFG ctx ()
  Var  :: Var ctx (F x a) -> Exp ctx x -> CFG ctx a
  Fix  :: (CFG (V x : F x a : ctx) a) -> Exp ctx x -> CFG ctx a
  Guard :: Exp ctx Bool -> CFG ctx ()

simplify :: CFG ctx a -> CFG ctx a
simplify (Seq a b) =
  case (simplify a, simplify b) of
    (Fail, _) -> Fail
    (_, Fail) -> Fail
    (Done x, y) -> apE0 x y
    (a', b') -> Seq a' b'
simplify (Or a b) =
  case (simplify a, simplify b) of
    (Fail, x) -> x
    (x, Fail) -> x
    (a', b') -> Or a' b'
simplify (Fix x e) = Fix (simplify x) e
simplify x = x

instance Show (CFG ctx a) where
  show Fail = "Fail"
  show (Or x y) = "Or (" ++ show x ++ ") (" ++ show y ++ ")"
  show (Done e) = "Done (" ++ show e ++ ")"
  show (Seq x y) = "Seq (" ++ show x ++ ") (" ++ show y ++ ")"
  show (Char c) = "Char " ++ show c
  show (Fix p e) = "Fix (" ++ show p ++ ") (" ++ show e ++ ")"
  show (Var v e) = "Var (" ++ show v ++ ") (" ++ show e ++ ")"
  show (Guard e) = "Guard (" ++ show e ++ ")"

data Syn ctx t where
  SV :: Exp ctx x -> Syn ctx (V x)
  SF :: CFG (V x : ctx) y -> Syn ctx (F x y)

thereSyn :: Syn ctx a -> Syn (x:ctx) a
thereSyn (SV x) = SV (thereExp x)
thereSyn (SF f) = SF (wk (\case HereV -> HereV; There v -> There (There v)) f)

getSV :: Syn ctx (V a) -> Exp ctx a
getSV (SV x) = x

getSF :: Syn ctx (F a b) -> CFG (V a : ctx) b
getSF (SF x) = x

varToSyn :: Var ctx a -> Syn ctx a
varToSyn HereV = SV hereExp
varToSyn HereF = SF (Var (There HereF) hereExp)
varToSyn (There v) = thereSyn (varToSyn v)

substExp :: (forall x. Var ctx x -> Syn ctx' x) -> Exp ctx a -> Exp ctx' a
substExp _ (ENil x) = ENil x
substExp f (ECons v xs) = substExp f xs <*> getSV (f v)

type family xs ++ ys where
  '[] ++ ys = ys
  (x : xs) ++ ys = x : (xs ++ ys)

data List' xs where
  Nil' :: List' '[]
  Cons' :: List' xs -> List' (x : xs)

varSplit :: List' pre -> List' ctx -> Var (pre ++ ctx) a -> Either (Var pre a) (Var ctx a)
varSplit Nil' _ x = Right x
varSplit (Cons' _) _ HereV = Left HereV
varSplit (Cons' _) _ HereF = Left HereF
varSplit (Cons' l) l' (There v) = case varSplit l l' v of
  Left x -> Left (There x)
  Right x -> Right x

near :: List' pre -> List' ctx -> Var pre a -> Var (pre ++ ctx) a
near Nil' _ v = case v of {}
near (Cons' _) _ HereV = HereV
near (Cons' _) _ HereF = HereF
near (Cons' l) l' (There v) = There (near l l' v)

far :: List' pre -> List' ctx -> Var ctx a -> Var (pre ++ ctx) a
far Nil' _ v = v
far (Cons' l) l' v = There (far l l' v)

apEE :: forall pre ctx a b. List' pre -> List' ctx -> Exp (pre ++ ctx) a -> Exp (pre ++ (V a : ctx)) b -> Exp (pre ++ ctx) b
apEE _ _ _ (ENil x) = ENil x
apEE l l' e (ECons v xs) =
  case varSplit l (Cons' @_ @(V a) l') v of
    Left v' -> ECons (near l l' v') (apEE l l' e xs)
    Right HereV -> flip ($) <$> e <*> apEE l l' e xs
    Right (There v') -> ECons (far l l' v') (apEE l l' e xs)

apE :: forall pre ctx a b. List' pre -> List' ctx -> Exp (pre ++ ctx) a -> CFG (pre ++ (V a : ctx)) b -> CFG (pre ++ ctx) b
apE _ _ _ Fail = Fail
apE l l' e (Or x y) = Or (apE l l' e x) (apE l l' e y)
apE l l' e (Done x) = Done (apEE l l' e x)
apE l l' e (Seq x y) = Seq (apE l l' e x) (apE (Cons' l) l' (substExp (varToSyn . There) e) y)
apE _ _ _ (Char c) = Char c
apE l l' e (Var v e') =
  case varSplit l (Cons' @_ @(V a) l') v of
    Left v' -> Var (near l l' v') (apEE l l' e e')
    Right (There v') -> Var (far l l' v') (apEE l l' e e')
apE l l' e (Fix x e') = Fix (apE (Cons' (Cons' l)) l' (substExp (varToSyn . There . There) e) x) (apEE l l' e e')
apE l l' e (Guard e') = Guard (apEE l l' e e')

apE0 :: Exp ctx a -> CFG (V a : ctx) b -> CFG ctx b
apE0 = apE Nil' undefined

subst :: (forall x. Var ctx x -> Syn ctx' x) -> CFG ctx a -> CFG ctx' a
-- subst _ cfg | traceShow ("subst", cfg) False = undefined
subst _ Fail = Fail
subst f (Or x y) = Or (subst f x) (subst f y)
subst f (Done x) = Done (substExp f x)
subst f (Seq x y) = Seq (subst f x) (subst (\case HereV -> SV hereExp; There v -> thereSyn (f v)) y)
subst _ (Char c) = Char c
subst f (Var v e) =
  -- subst (\case HereV -> SV $ substExp f e; There v' -> varToSyn v') (getSF (f v))
  apE Nil' undefined (substExp f e) (getSF (f v))
subst f (Fix p x) = Fix (subst (\case 
  HereV -> varToSyn HereV
  There HereF -> varToSyn (There HereF)
  There (There v) -> thereSyn (thereSyn (f v))) p) (substExp f x)
subst f (Guard e) = Guard (substExp f e)

wk :: (forall x. Var ctx x -> Var ctx' x) -> CFG ctx a -> CFG ctx' a
wk _ Fail = Fail
wk f (Or x y) = Or (wk f x) (wk f y)
wk f (Done x) = Done (substExp (varToSyn . f) x)
wk f (Seq x y) = Seq (wk f x) (wk (\case HereV -> HereV; There v -> There (f v)) y)
wk _ (Char c) = Char c
wk f (Var v e) = Var (f v) (substExp (varToSyn . f) e)
wk f (Guard e) = Guard (substExp (varToSyn . f) e)
wk f (Fix x e) = Fix (wk (\case HereV -> HereV; There HereF -> There HereF; There (There v) -> There (There (f v))) x) (substExp (varToSyn . f) e)
-- wk f = subst (varToSyn . f)

type family Sem t where
  Sem (V x) = x
  Sem (F x y) = x -> [y]

evalExp :: (forall x. Var ctx x -> Sem x) -> Exp ctx a -> Sem (V a)
evalExp _ (ENil x) = x
evalExp f (ECons v x) = evalExp f x (f v)

nullable' :: (forall x y. Var ctx (F x y) -> [(Exp (V x : ctx) Bool, Exp (V x : ctx) y)]) -> CFG ctx a -> [(Exp ctx Bool, Exp ctx a)]
nullable' _ Fail = []
nullable' ev (Or p q) = nullable' ev p ++ nullable' ev q
nullable' _ (Done x) = [(ENil True, x)]
nullable' ev (Seq p q) = do
  (gx,ex) <- nullable' ev p
  (gy,ey) <- nullable' ev (apE0 ex q)
  pure (liftA2 (&&) gx gy, ey)
nullable' _ (Char _) = []
nullable' ev (Guard e) = [(e, ENil ())]
nullable' ev (Var v e) = map (\(x,y) -> (apEE Nil' undefined e x, apEE Nil' undefined e y)) (ev v)
nullable' ev (Fix x e) = _ $ nullable' (\case There HereF -> []; There (There v) -> _ $ ev v) x

nullable :: (forall x. Var ctx x -> Sem x) -> CFG ctx a -> [a]
-- nullable _ cfg | traceShow ("nullable", cfg) False = undefined
nullable _ Fail = []
nullable ev (Or p q) = nullable ev p ++ nullable ev q
nullable ev (Done x) = [ evalExp ev x ]
nullable ev (Seq p q) = do
  x <- nullable ev p
  nullable (\case HereV -> x; There v -> ev v) q 
nullable _ (Char _) = []
nullable ev (Var v e) = ev v (evalExp ev e)
nullable ev (Fix p e) = nullable (\case HereV -> evalExp ev e; There HereF -> const []; There (There v') -> ev v') p
nullable ev (Guard e) = [() | evalExp ev e]

wk3 :: CFG (V x : F y z : ctx) a -> CFG (V x : F y z : w : ctx) a
wk3 = wk $ \case
  HereV -> HereV
  There HereF -> There HereF
  There (There v) -> There (There (There v))

data D ctx a where
  DV :: a -> D ctx (V a)
  DF :: (x -> [y]) -> Var ctx (F x y) -> D ctx (F x y)

dsem :: D ctx a -> Sem a
dsem (DV sem {- _ f -}) = sem
dsem (DF sem _)= sem

df :: D ctx (F a b) -> Var ctx (F a b)
df (DF _ syn) = syn

getD :: D ctx (V a) -> a
getD (DV x) = x

dExp :: (forall x. Var ctx x -> D ctx x) -> Exp ctx a -> D ctx (V a)
dExp _ (ENil x) = DV x
dExp ev (ECons x xs) = DV $ getD (dExp ev xs) $ getD (ev x) 

wkD :: (forall x. Var ctx x -> Var ctx' x) -> D ctx a -> D ctx' a
wkD _ (DV x) = DV x
wkD w (DF x v) = DF x (w v)

derivative :: forall ctx a. CFG ctx a -> (forall x. Var ctx x -> D ctx x)
           -> Char -> CFG ctx a
-- derivative cfg _ c | traceShow ("derivative", cfg, c) False = undefined
derivative Fail _ _ = Fail
derivative (Or p q) ev c = Or (derivative p ev c) (derivative q ev c)
derivative (Done _) _ _ = Fail
derivative (Seq p q) ev c = Or (Seq (derivative p ev c) q)
  (foldr Or Fail [derivative (apE0 (ENil x) q) ev c | x <- nullable (dsem . ev) p])
derivative (Char c') _ c = if c == c' then Done (ENil ()) else Fail
derivative (Var v x) ev _ = Var (df (ev v)) x
derivative (Fix @x p x) ev c =
  subst
    (\case
      HereF -> SF (Fix (wk3 p) hereExp)
      There v -> varToSyn v)
    (Fix
      (derivative
        (wk (\case HereV -> HereV; There v -> There (There v)) p)
        (\case
          HereV -> wkD (There . There . There) (dExp ev x)
          There HereF -> error "impossible"
          There (There HereF) ->
            DF
            ( \x' ->
              nullable
                (\case
                  HereV -> x'
                  There v -> dsem (ev v))
                (Fix (wk3 p) hereExp)
            )
            (There HereF)
          There (There (There v)) -> wkD (There . There . There) (ev v)
        )
        c)
      (thereExp x))
derivative (Guard _) _ _ = Fail

parse :: CFG '[] a -> String -> [a]
parse s [] = nullable (\case) s
parse s (x:xs) = parse (derivative s (\case) x) xs

digit :: CFG ctx Int
digit = foldr Or Fail [Seq (Char (intToDigit x)) (Done (ENil x)) | x <- [0..9]]

dots :: CFG ctx ()
dots = Fix (Seq (Char '.') (Var (There (There HereF)) (ENil ()))) (ENil ())

ndots :: CFG ctx ()
ndots = Seq digit $ Fix 
  (Or 
    (Seq (Guard (ECons HereV (ENil (> 0)))) 
      (Seq (Char '.') (Var (There (There (There HereF))) (ECons (There (There HereV)) (ENil (subtract 1))))))
    (Guard (ECons HereV (ENil (== 0)))))
  hereExp

ndots' :: CFG ctx ()
ndots' = Seq digit $ Fix 
  (Or 
    (Seq (Guard (ECons HereV (ENil (> 0)))) 
      (Seq (Var (There (There HereF)) (ECons (There HereV) (ENil (subtract 1)))) (Char '.')))
    (Guard (ECons HereV (ENil (== 0)))))
  hereExp

-- ndots = Seq digit (Fix (\i -> Or 
--   (Seq (guard (i > 0)) (\() -> Seq (Char '.') (\() -> Var Here (i - 1))))
--   (guard (i == 0))
--   ))

data X = X | Add X X deriving Show

ex = Fix 
  (Or 
    (Seq (Char 'x') (Done (ENil X))) 
    (Seq (Guard hereExp) 
      (Seq 
        (Var (There (There HereF)) (ENil False))
        (Seq (Char '+')
          (Seq 
            (Var (There (There (There (There HereF)))) (ENil True))
            (Done (ECons HereV (ECons (There (There HereV)) (ENil Add)))))))))
  (ENil True)

main :: IO ()
main = print $ simplify $ derivative dots (\case) '.'

-- Fix (Or (Seq (Char 'x') (Done (ENil (X)))) (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>)))))))))) (ENil (True))

-- x
-- Fix 
--  (Or 
--   (Done (ENil (X)))
--   (Seq (Var (There HereF) (ENil (False)))
--    (Seq (Char '+')
--    (Seq 
--     (Fix
--      (Or (Seq (Char 'x') (Done (ENil (X))))
--          (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (There (There HereV)) (ECons (HereV) (ENil (<Fun>))))))))))
--      (ENil (True)))
--    (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>)))))))))
--  (ENil (True))


-- x+
-- Fix 
--  (Or
--   (Seq (Var (There HereF) (ENil (False)))
--    (Seq (Char '+')
--    (Seq (Fix (Or (Seq (Char 'x') (Done (ENil (X)))) (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (There (There HereV)) (ECons (HereV) (ENil (<Fun>)))))))))) (ENil (True)))
--    (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>))))))))
--   (Seq (Done (ENil (()))) 
--    (Seq (Fix (Or (Seq (Char 'x') (Done (ENil (X)))) (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (There (There HereV)) (ECons (HereV) (ENil (<Fun>)))))))))) (ENil (True)))
--    (Done (ECons (HereV) (ENil (<Fun>)))))))
--  (ENil (True))

-- x+x
-- Fix (Or (Seq (Var (There HereF) (ENil (False))) (Seq (Char '+') (Seq (Fix (Or (Seq (Char 'x') (Done (ENil (X)))) (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (There (There HereV)) (ECons (HereV) (ENil (<Fun>)))))))))) (ENil (True))) (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>)))))))) (Seq (Fix (Or (Done (ENil (X))) (Seq (Var (There HereF) (ENil (False))) (Seq (Char '+') (Seq (Fix (Or (Seq (Char 'x') (Done (ENil (X)))) (Seq (Guard (ECons (HereV) (ENil (<Fun>)))) (Seq (Var (There (There HereF)) (ENil (False))) (Seq (Char '+') (Seq (Var (There (There (There (There HereF)))) (ENil (True))) (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>)))))))))) (ENil (True))) (Done (ECons (There (There HereV)) (ECons (HereV) (ENil (<Fun>))))))))) (ENil (True))) (Done (ECons (HereV) (ENil (<Fun>)))))) (ENil (True))

-- Fix
--   (Or
--      (Seq (Var (There HereF) (ENil (False)))
--       (Seq (Char '+')
--       (Seq
--          (Fix
--             (Or
--                (Seq (Char 'x') (Done (ENil (X))))
--                (Seq
--                   (Guard (ECons (HereV) (ENil (<Fun>))))
--                   (Seq
--                      (Var (There (There HereF)) (ENil (False)))
--                      (Seq
--                         (Char '+')
--                         (Seq
--                            (Var
--                               (There (There (There (There HereF))))
--                               (ENil (True)))
--                            (Done
--                               (ECons
--                                  (There (There HereV))
--                                  (ECons (HereV) (ENil (<Fun>))))))))))
--             (ENil (True)))
--       (Done (ECons (HereV) (ECons (There (There HereV)) (ENil (<Fun>))))))))
--      (Seq
--         (Fix
--            (Or
--               (Done (ENil (X)))
--               (Seq
--                  (Var (There HereF) (ENil (False)))
--                  (Seq
--                     (Char '+')
--                     (Seq
--                        (Fix
--                           (Or
--                              (Seq (Char 'x') (Done (ENil (X))))
--                              (Seq
--                                 (Guard (ECons (HereV) (ENil (<Fun>))))
--                                 (Seq
--                                    (Var (There (There HereF)) (ENil (False)))
--                                    (Seq
--                                       (Char '+')
--                                       (Seq
--                                          (Var
--                                             (There
--                                                (There (There (There HereF))))
--                                             (ENil (True)))
--                                          (Done
--                                             (ECons
--                                                (HereV)
--                                                (ECons
--                                                   (There (There HereV))
--                                                   (ENil (<Fun>))))))))))
--                           (ENil (True)))
--                        (Done
--                           (ECons
--                              (There (There HereV))
--                              (ECons (HereV) (ENil (<Fun>)))))))))
--            (ENil (True)))
--         (Done (ECons (HereV) (ENil (<Fun>))))))
--   (ENil (True))
