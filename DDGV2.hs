{- cabal:
build-depends: base, recover-rtti, tasty-bench, tasty-bench-fit
-}
{-# LANGUAGE GHC2021, GADTs, DataKinds, LambdaCase, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- DATA-DEPENDENT PARSING WITH VARIABLES

import Prelude hiding (Monad (..))
import Data.Char (intToDigit)
import Data.Kind (Type)
-- import Debug.RecoverRTTI
-- import Test.Tasty.Bench.Fit
-- import Test.Tasty.Bench
import Data.Type.Equality
import Data.Bifunctor
import Data.List (intercalate)

type Var :: [k] -> k -> Type
data Var ctx a where
  Here :: Var (a : ctx) a
  There :: Var ctx a -> Var (b : ctx) a

varInt :: Var xs a -> Int
varInt Here = 0
varInt (There v) = varInt v + 1

instance Show (Var ctx a) where
  show v = show (varInt v)

data EAtom a where
  EABool :: Bool -> EAtom Bool
  EAInt :: Int -> EAtom Int
  EAUnit :: EAtom ()
  EAEq :: EAtom (Int -> Int -> Bool)
  EAGt :: EAtom (Int -> Int -> Bool)
  EASub :: EAtom (Int -> Int -> Int)
  EAAnd :: EAtom (Bool -> Bool -> Bool)
deriving instance Show (EAtom a)

type Exp :: [Type] -> Type -> Type
data Exp ctx a where
  EHs :: a -> Exp ctx a
  EVar :: Var ctx x -> Exp ctx x
  -- EAp :: forall ctx a x. Exp ctx x -> Exp ctx (x -> a) -> Exp ctx a
  EAtom :: EAtom a -> Exp ctx a
  ELam :: Exp (a : ctx) b -> Exp ctx (a -> b)
  EAp :: Exp ctx (a -> b) -> Exp ctx a -> Exp ctx b

-- eap :: Exp ctx x -> Exp ctx (x -> a) -> Exp ctx a
-- eap (ENil x) (ENil f) = ENil (f x)
-- eap x (EAtom EAFlipAp) = _ x
-- eap (EAtom EAFlipAp) x = _ x
-- eap x y = EAp x y

instance Functor (Exp ctx) where
  fmap f x = EAp (EHs f) x

instance Applicative (Exp ctx) where
  pure = EHs
  p <*> q = EAp p q
  -- ENil f <*> x = fmap f x
  -- Eq0 <*> x = _ x
  -- Gt0 <*> x = _
  -- EVar v <*> x = _
  -- eap x xs <*> y = eap x (flip <$> xs <*> y)

ehere :: Exp (x : vs) x
ehere = EVar Here

ethere :: Exp vs a -> Exp (x : vs) a
ethere = wkE There

evar :: Var vs a -> Exp vs a
evar = EVar

-- showExpList :: Exp vs a -> [String]
-- showExpList ENil{} = []
-- showExpList Gt0 = ["Gt0"]
-- showExpList Eq0 = 
-- showExpList (eap x xs) = showExpList x ++ showExpList xs

instance Show (Exp ctx a) where
  -- show (ENil x) = "ENil (" ++ anythingToString x ++ ")"
  show EHs{} = "ENil{}"
  show (EVar v) = show v
  show (EAp x xs) = "EAp (" ++ show x ++ ") (" ++ show xs ++ ")"
  show (EAtom a) = show a
  show (ELam x) = "ELam (" ++ show x ++ ")"
  -- show x = "[" ++ intercalate "," (showExpList x) ++ "]"

eqVar :: Var vs a -> Var vs b -> Maybe (a :~: b)
eqVar Here Here = Just Refl
eqVar (There v) (There w) = eqVar v w
eqVar _ _ = Nothing

-- this optimization improves dotsl
simplifyE :: Exp vs a -> Exp vs a
simplifyE (EAp (EVar v) (EAp (EVar w) xs)) | Just Refl <- eqVar v w = EAp (evar v) xs
simplifyE (EAp (EAp (EAtom EASub) (EAtom x)) (EAtom y)) = EAtom (EAInt (eaeval y - eaeval x))
simplifyE (EAp (EAp (EAtom EASub) (EAtom x)) (EAp (EAp (EAtom EASub) (EAtom y)) z)) = EAtom EASub <*> EAtom (EAInt (eaeval x + eaeval y)) <*> z
simplifyE (EAp (EAp (EAtom EAEq) (EAtom x)) (EAtom y)) = EAtom (EABool (eaeval x == eaeval y))
simplifyE (EAp x y) = EAp (simplifyE x) (simplifyE y)
simplifyE (EAtom x) = EAtom x
simplifyE (EHs x) = EHs x
simplifyE (EVar v) = EVar v
simplifyE (ELam x) = ELam (simplifyE x)

substE :: (forall x. Var vs x -> Exp vs' x) -> Exp vs a -> Exp vs' a
substE _ (EHs x) = EHs x
substE f (EVar v) = f v
substE _ (EAtom a) = EAtom a
substE f (EAp x xs) = substE f x <*> substE f xs
substE f (ELam x) = ELam (substE (\case Here -> ehere; There v -> ethere $ f v) x)

apEE :: Exp (a : vs) b -> Exp vs a -> Exp vs b
apEE x y = substE (\case Here -> y; There v -> evar v) x

wkE :: (forall x. Var vs x -> Var vs' x) -> Exp vs a -> Exp vs' a
wkE f = substE (evar . f)

eaeval :: EAtom a -> a
eaeval (EABool b) = b
eaeval (EAInt n) = n
eaeval EAUnit = ()
eaeval EAGt = (>)
eaeval EAEq = (==)
eaeval EASub = subtract
eaeval EAAnd = (&&)

eeval :: Exp '[] a -> a
eeval = eeval' (\case)

eeval' :: (forall x. Var vs x -> x) -> Exp vs a -> a
eeval' _ (EAtom a) = eaeval a
eeval' _ (EHs b) = b
eeval' ev (EAp x y) = eeval' ev x (eeval' ev y)
eeval' ev (EVar v) = ev v
eeval' ev (ELam x) = \x' -> eeval' (\case Here -> x'; There v -> ev v) x

type CFG :: [(Type,Type)] -> [Type] -> Type -> Type
data CFG nts vs a where
  Fail :: CFG nts vs a
  Or   :: CFG nts vs a -> CFG nts vs a -> CFG nts vs a
  Done :: Exp vs a -> CFG nts vs a
  Seq  :: CFG nts vs a -> CFG nts (a : vs) b -> CFG nts vs b
  Char :: Char -> CFG nts vs ()
  Var  :: Var nts '(x, a) -> Exp vs x -> CFG nts vs a
  Fix  :: CFG ('(x,a):nts) (x:vs) a -> Exp vs x -> CFG nts vs a
  Guard :: Exp vs Bool -> CFG nts vs ()
  Let  :: CFG nts (x : vs) y -> CFG ('(x,y):nts) vs a -> CFG nts vs a

data Thin xs ys where
  EndDrop :: Thin xs '[]
  EndKeep :: Thin xs xs
  Keep :: Thin xs ys -> Thin (x : xs) (x : ys)
  Drop :: Thin xs ys -> Thin (x : xs) ys

data CombineThin xs ys zs = forall xs'. CombineThin (Thin xs xs') (Thin xs' ys) (Thin xs' zs)

combineThin :: Thin xs ys -> Thin xs zs -> CombineThin xs ys zs
combineThin EndDrop t = CombineThin t EndDrop EndKeep
combineThin t EndDrop = CombineThin t EndKeep EndDrop
combineThin EndKeep t = CombineThin EndKeep EndKeep t
combineThin t EndKeep = CombineThin EndKeep t EndKeep
combineThin (Keep t) (Keep t') =
  case combineThin t t' of
    CombineThin x y z -> CombineThin (Keep x) (Keep y) (Keep z)
combineThin (Keep t) (Drop t') =
  case combineThin t t' of
    CombineThin x y z -> CombineThin (Keep x) (Keep y) (Drop z)
combineThin (Drop t) (Keep t') =
  case combineThin t t' of
    CombineThin x y z -> CombineThin (Keep x) (Drop y) (Keep z)
combineThin (Drop t) (Drop t') =
  case combineThin t t' of
    CombineThin x y z -> CombineThin (Drop x) y z

data Unused nts vs a = forall nts'. Unused (CFG nts' vs a) (Thin nts nts')
combine
  :: (forall nts'. CFG nts' vsa a -> CFG nts' vsb b -> CFG nts' vsc c)
  -> Unused nts vsa a -> Unused nts vsb b -> Unused nts vsc c
combine f (Unused x t) (Unused y t') =
  case combineThin t t' of
    CombineThin tt tx ty -> Unused (f (wkNts (apThin tx) x) (wkNts (apThin ty) y)) tt

varToThin :: Var nts a -> Thin nts '[a]
varToThin Here = Keep EndDrop
varToThin (There v) = Drop (varToThin v)

unused :: CFG nts vs a -> Unused nts vs a
unused Fail = Unused Fail EndDrop
unused (Or x y) = combine Or (unused x) (unused y)
unused (Done x) = Unused (Done x) EndDrop
unused (Seq x y) = combine Seq (unused x) (unused y)
unused (Char c) = Unused (Char c) EndDrop
unused (Var v e) = Unused (Var Here e) (varToThin v)
unused (Guard e) = Unused (Guard e) EndDrop
unused (Fix p e) =
  case unused p of
    Unused p' EndDrop  -> Unused (Fix (wkNts There p') e) EndDrop
    Unused p' EndKeep    -> Unused (Fix p' e) EndKeep
    Unused p' (Drop t) -> Unused (Fix (wkNts There p') e) t
    Unused p' (Keep t) -> Unused (Fix p' e) t
unused (Let p q) =
  case (unused p, unused q) of
    (Unused p' tp, Unused q' EndDrop) -> Unused (Let p' (wkNts (\case) q')) tp
    (Unused p' tp, Unused q' EndKeep) -> Unused (Let (wkNts (apThin tp) p') q') EndKeep
    (Unused p' tp, Unused q' (Drop tq)) ->
      case combineThin tp tq of
        CombineThin tt tp' tq' ->
          Unused
            (Let
              (wkNts (apThin tp') p')
              (wkNts (There . apThin tq') q'))
            tt
    (Unused p' tp, Unused q' (Keep tq)) ->
      case combineThin tp tq of
        CombineThin tt tp' tq' ->
          Unused
            (Let
              (wkNts (apThin tp') p')
              (wkNts (\case Here -> Here; There v -> There $ apThin tq' v) q'))
            tt

apThin :: Thin xs ys -> Var ys a -> Var xs a
apThin EndDrop x = case x of {}
apThin EndKeep x = x
apThin (Drop t) x = There (apThin t x)
apThin (Keep t) (There x) = There (apThin t x)
apThin (Keep _) Here = Here

simplify :: CFG nts vs a -> CFG nts vs a
simplify (Seq a b) =
  case (simplify a, simplify b) of
    (Fail, _) -> Fail
    (_, Fail) -> Fail
    (Done x, y) -> apEG y x
    (a', b') -> Seq a' b'
simplify (Or a b) =
  case (simplify a, simplify b) of
    (Fail, x) -> x
    (x, Fail) -> x
    (a', b') -> Or a' b'
simplify (Fix x e) =
  -- this optimization improves dotsr
  case unused x of
    Unused x' EndDrop -> apEG (wkNts (\case) (simplify x')) (simplifyE e)
    Unused x' (Drop t) -> apEG (wkNts (apThin t) (simplify x')) (simplifyE e)
    _ -> Fix (simplify x) (simplifyE e)
simplify (Guard e) = Guard (simplifyE e)
-- case simplifyE e of
--   EHs b -> if b then Done (EAtom EAUnit) else Fail
--   EAtom (EABool b) -> if b then Done (EAtom EAUnit) else Fail
--   e' -> Guard e'
simplify (Done e) = Done (simplifyE e)
-- simplify (Let (Let p q) r) = Let p (Let (_ q) (_ r))
simplify (Let p q) =
  case unused (simplify q) of
    Unused q' EndDrop -> wkNts (\case) q'
    Unused q' (Drop t) -> wkNts (apThin t) q'
    _ -> 
      case simplify q of
        Var Here e -> simplify (apEG p e)
        q' -> Let (simplify p) q'
simplify (Char c) = Char c
simplify Fail = Fail
simplify (Var v e) = Var v (simplifyE e)

showSeqs :: CFG nts vs a -> [String]
showSeqs (Seq p q) = show p : showSeqs q
showSeqs x = [ show x ]

instance Show (CFG nts vs a) where
  show Fail = "Fail"
  show (Or x y) = "Or (" ++ show x ++ ") (" ++ show y ++ ")"
  show (Done e) = "Done (" ++ show e ++ ")"
  show x@Seq{} = "do {" ++ intercalate "; " (showSeqs x) ++ "}"
  -- "Seq (" ++ show x ++ ") (" ++ show y ++ ")"
  show (Char c) = "Char " ++ show c
  show (Fix p e) = "Fix (" ++ show p ++ ") (" ++ show e ++ ")"
  show (Var v e) = "Var (" ++ show v ++ ") (" ++ show e ++ ")"
  show (Guard e) = "Guard (" ++ show e ++ ")"
  show (Let p q) = "Let (" ++ show p ++ ") (" ++ show q ++ ")"

substVs :: (forall x. Var vs x -> Exp vs' x) -> CFG nts vs a -> CFG nts vs' a
substVs _ Fail = Fail
substVs f (Or p q) = Or (substVs f p) (substVs f q)
substVs f (Done x) = Done (substE f x)
substVs f (Seq p q) = Seq (substVs f p) (substVs (\case Here -> ehere; There v -> ethere $ f v) q)
substVs _ (Char c) = Char c
substVs f (Var v e) = Var v (substE f e)
substVs f (Fix p e) = Fix (substVs (\case Here -> ehere; There v -> ethere (f v)) p) (substE f e)
substVs f (Guard e) = Guard (substE f e)
substVs f (Let p q) = Let (substVs (\case Here -> ehere; There v -> ethere (f v)) p) (substVs f q)

wkVs :: (forall x. Var vs x -> Var vs' x) -> CFG nts vs a -> CFG nts vs' a
wkVs f = substVs (evar . f)

substNts :: (forall x y. Var nts '(x,y) -> CFG nts' (x:vs) y) -> CFG nts vs a -> CFG nts' vs a
substNts _ Fail = Fail
substNts f (Or p q) = Or (substNts f p) (substNts f q)
substNts _ (Done x) = Done x
substNts f (Seq p q) = Seq (substNts f p) (substNts (wkVs (\case Here -> Here; There v -> There (There v)) . f) q)
substNts _ (Char c) = Char c
substNts f (Var v e) = apEG (f v) e
substNts f (Fix p e) = Fix (substNts (\case Here -> Var Here ehere; There v -> wkNts There $ wkVs (\case Here -> Here; There v' -> There (There v')) $ f v) p) e
substNts _ (Guard e) = Guard e
substNts f (Let p q) = Let (substNts (wkVs (\case Here -> Here; There v -> There (There v)) . f) p) (substNts (\case Here -> Var Here ehere; There v -> wkNts There (f v)) q)

wkNts :: (forall x y. Var nts '(x,y) -> Var nts' '(x,y)) -> CFG nts vs a -> CFG nts' vs a
wkNts f = substNts ((\v -> Var v ehere) . f)

apEG :: CFG nts (a : vs) b -> Exp vs a -> CFG nts vs b
apEG p e = substVs (\case Here -> e; There v -> evar v) p

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

both1 :: (forall x. f x -> g x) -> (f a, f b) -> (g a, g b)
both1 f (x, y) = (f x, f y)

-- 

eand :: Exp vs Bool -> Exp vs Bool -> Exp vs Bool
eand (EAtom (EABool True)) y = y
eand x (EAtom (EABool True)) = x
eand (EAtom (EABool False)) _ = EAtom (EABool False)
eand _ (EAtom (EABool False)) = EAtom (EABool False)
eand x y = EAtom EAAnd <*> x <*> y

nullable :: (forall x y. Var nts '(x, y) -> [(Exp (x:vs) Bool, Exp (x:vs) y)]) -> CFG nts vs a -> [(Exp vs Bool, Exp vs a)]
nullable _ Fail = []
nullable ev (Or p q) = nullable ev p ++ nullable ev q
nullable _ (Done x) = [(EAtom (EABool True), x)]
nullable ev (Seq p q) = do
  (xg,xe) <- nullable ev p
  (yg,ye) <- nullable ev (apEG q xe)
  pure (eand xg yg, ye)
nullable _ (Char _) = []
nullable _ (Guard e) = [(e, EAtom EAUnit)]
nullable ev (Var v e) = map (\(x,y) -> (apEE x e, apEE y e)) (ev v)
nullable ev (Fix x e) = map (both1 (`apEE` e)) $ nullable (\case Here -> []; There v -> map (both1 (wkE (\case Here -> Here; There v' -> There (There v')))) $ ev v) x
nullable ev (Let p q) =
  let x = nullable (map (both1 (wkE (\case Here -> Here; There v -> There (There v)))) . ev) p
  in nullable (\case Here -> x; There v -> ev v) q

nullable0 :: CFG '[] '[] a -> [a]
nullable0 x = do
  (b, xe) <- nullable (\case) x
  [eeval xe | eeval b]

onTail :: (forall x. Var xs x -> Var xs' x) -> Var (a:xs) b -> Var (a:xs') b
onTail _ Here = Here
onTail f (There v) = There (f v)

guard :: Exp vs Bool -> CFG nts vs ()
guard (EHs b) = if b then Done (EAtom EAUnit) else Fail
guard (EAtom (EABool b)) = if b then Done (EAtom EAUnit) else Fail
guard e = Guard e

derivative :: CFG nts vs a
  -> (forall x y. Var nts '(x,y) -> ([(Exp (x:vs) Bool, Exp (x:vs) y)],Var nts '(x,y)))
  -> Char -> CFG nts vs a
-- derivative cfg _ c | traceShow ("derivative", cfg, c) False = undefined
derivative Fail _ _ = Fail
derivative (Or p q) nts c = Or (derivative p nts c) (derivative q nts c)
derivative (Done _) _ _ = Fail
derivative (Seq p q) nts c = Or
  (foldr Or Fail [Seq (guard xg) (wkVs There $ derivative (apEG q xe) nts c) | (xg,xe) <- nullable (fst . nts) p])
  (Seq (derivative p nts c) q)
derivative (Char c') _ c = if c == c' then Done (EAtom EAUnit) else Fail
derivative (Var v x) nts _ = Var (snd (nts v)) x
derivative (Fix @x p x) nts c =
  Let
    (Fix (wkVs (onTail There) p) ehere)
  -- substNts (\case Here -> Fix (wkVs (\case Here -> Here; There v -> There (There v)) p) (ECons Here (ENil id)); There v -> Var v ehere) $
    (Fix
      (derivative
        (wkNts There p)
        (\case
          Here -> error "impossible"
          There Here ->
            (nullable (map (both1 (wkE (onTail (There . There)))) . fst . nts) (Fix (wkVs (onTail (There . There)) p) ehere)
            , Here
            )
          There (There v) -> bimap (map (both1 (wkE (onTail There)))) (There . There) (nts v)
        )
        c)
      x)
derivative (Guard _) _ _ = Fail
derivative (Let @_ @x @vs (Fix @_ @_ p (EVar Here)) q) nts c =
  Let (Fix p ehere) $
  Let
    (Fix
      (derivative
        (wkNts There p)
        (\case
          Here -> error "impossible"
          There Here ->
            ( nullable (map (both1 (wkE (onTail (There . There . There)))) . fst . nts) (Fix (wkVs (onTail (There . There)) p) ehere)
            , Here
            )
          There (There v) -> bimap (map (both1 (wkE (onTail (There . There))))) (There . There) (nts v)
        )
        c)
      ehere)
    $
  derivative 
    (wkNts There q)
    (\case
      Here -> error "impossible"
      There Here -> (nullable (map (both1 (wkE (onTail There))) . fst . nts) (Fix p ehere), Here)
      There (There v) -> second (There . There) (nts v)
    )
    c
derivative (Let p q) nts c =
  Let p $
  Let
    (wkNts There $ derivative
      p
      (first (map (both1 (wkE (\case
        Here -> Here
        There v -> There (There v))))) . nts)
      c) $
  derivative
    (wkNts There q)
    (\case
      Here -> error "impossible"
      There Here ->
        (nullable (map (both1 (wkE (\case
          Here -> Here
          There v -> There (There v)))) . fst . nts) p
        ,Here)
      There (There v) -> fmap (There . There) (nts v))
    c

derivative0 :: CFG '[] '[] a -> Char -> CFG '[] '[] a
derivative0 g = derivative g (\case)

parse :: CFG '[] '[] a -> String -> [a]
parse s [] = nullable0 s
parse s (x:xs) = parse (simplify (derivative0 s x)) xs

digit :: CFG nts vs Int
digit = foldr Or Fail [Seq (Char (intToDigit x)) (Done (EAtom (EAInt x))) | x <- [0..9]]

dotsr :: Int -> CFG nts vs ()
dotsr n = Fix (Or
  (Seq (Char '.') (Var Here (EAtom EASub <*> EAtom (EAInt 1) <*> evar (There Here))))
  (Guard (EAtom EAEq <*> EAtom (EAInt 0) <*> evar Here))
  ) (EAtom (EAInt n))

-- X(n) = '.' X(n-1) | [n = 0]

dotsl :: Int -> CFG nts vs ()
dotsl n = Fix (Or
  (Seq (Var Here (EAtom EASub <*> EAtom (EAInt 1) <*> evar Here)) (Char '.'))
  (Guard (EAtom EAEq <*> EAtom (EAInt 0) <*> evar Here))
  ) (EAtom (EAInt n))

-- X(n) = X(n-1) '.' | [n = 0]
-- X(n) = X(n-1) '.' | [n = 1]
-- X(n) = X(n-1) '.' | [n = 2]
-- X(n) = X(n-1) '.' | [n = 3]
-- X(n) = X(n-1) '.' | [n = 4]

data X = X | Add X X deriving Show

type (<=) :: forall k. [k] -> [k] -> Type
type vs <= vs' = forall x. Var vs x -> Var vs' x

fix :: (forall nts' vs'. nts <= nts' -> Var nts' '(x,a) -> vs <= vs' -> Var vs' x -> CFG nts' vs' a) -> Exp vs x -> CFG nts vs a
fix f = Fix (f There Here There Here)

infixr 4 >>=
(>>=) :: CFG nts vs a -> (forall vs'. vs <= vs' -> Var vs' a -> CFG nts vs' b) -> CFG nts vs b
m >>= k = Seq m (k There Here)

return :: Var vs a -> CFG nts vs a
return v = Done (evar v)

infixr 4 >>
(>>) :: CFG nts vs a -> CFG nts vs b -> CFG nts vs b
m >> k = Seq m (wkVs There k)

infixr 3 <|>
(<|>) :: CFG nts vs a -> CFG nts vs a -> CFG nts vs a
(<|>) = Or

ex :: CFG nts vs X
ex = fix (\_ p _ b -> Char 'x' >>
                      Done (pure X)
                  <|> Guard (evar b) >>
                      Var p (EAtom (EABool False)) >>= \_ x ->
                      Char '+' >>
                      Var p (EAtom (EABool True)) >>= \e y ->
                      Done (Add <$> evar (e x) <*> evar y))
  (EAtom (EABool True))

-- main :: IO ()
-- main = defaultMain $
--   [ bench (show k) $ nf (\n -> parse (dotsr n) (replicate n '.')) k
--   | k <- [10,20..80]
--   ]
-- main = do
--   putStrLn "Start"
--   mapM_ print =<< fits (mkFitConfig (\n -> parse (dotsl (fromIntegral n)) (replicate (fromIntegral n) '.')) (10, 100))