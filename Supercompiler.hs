module Supercompiler where

import           Control.Monad
import           Control.Monad.Reader (Reader)
import qualified Control.Monad.Reader as R
import           Data.Bifunctor       (first)
import qualified Data.List            as L
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as M
import           Data.Maybe           (catMaybes)
import qualified Data.Tuple           as T (swap)

import           Debug.Trace          (traceShow)

---------------------------------------------------------------
-- Our language.
---------------------------------------------------------------

data E = Func String
       | App E E
       | Case E [(Pat, E)]
       | Let String E E
       | I Int
       | B Bool
       | Var String
       | Lam String E
       | Binop String E E
       | C String [E]
  deriving (Eq, Show)

data Pat = VarPat String
         | CPat String [Pat]
         | BPat Bool
  deriving (Eq, Show)

type Def = (String, E)

data Prg = Prg [Def] E
  deriving (Eq, Show)

type VarsM = Map String E
type DefsM = Map String E

lookupFunc :: String -> Reader DefsM E
lookupFunc x = R.ask >>= pure . (M.! x)

matchPat :: VarsM -> (Pat, E) -> Maybe VarsM
matchPat m (VarPat x, e)       = Just $ M.insert x e m
matchPat m (BPat b, B b')      = if b == b' then Just m else Nothing
matchPat m (CPat cp ps, C c s) = do
    when (length ps /= length s || cp /= c) $ fail "Can't pattern match."
    foldM matchPat m $ zip ps s
matchPat _ _              = Nothing

patVars :: Pat -> [String]
patVars (VarPat x)  = [x]
patVars (CPat _ ps) = concatMap patVars ps
patVars _           = []

sub :: E -> String -> E -> E
sub f@(Func _) _ _ = f
sub (App l r) k v  = App l' r'
  where
    l' = sub l k v
    r' = sub r k v
sub (Case e ps) k v =
    Case (sub e k v) $ fmap (\(p, e') -> if k `elem` patVars p then (p, e') else (p, sub e' k v)) ps
sub (Let x e e') k v = if x /= k then Let x subE (sub e' k v) else Let x subE e'
  where
    subE = sub e k v
sub i@I{} _ _ = i
sub b@B{} _ _ = b
sub (Var x) k v   = if x == k then v else Var x
sub (Lam x e) k v = if x == k then Lam x e else Lam x (sub e k v)
sub (Binop x l r) k v = Binop x (sub l k v) (sub r k v)
sub (C x xs) k v      = C x $ fmap (\x' -> sub x' k v) xs

evaluateE :: E -> Reader DefsM E
evaluateE e = evaluateE' e
  where
    evaluateE' :: E -> Reader DefsM E
    evaluateE' (Func x)          = lookupFunc x
    evaluateE' (App (Lam x b) r) = evaluateE $ sub b x r
    evaluateE' (App l r)         = do
        l' <- evaluateE l
        if l == l'
        then fail "Can't evaluate."
        else evaluateE $ App l' r
    evaluateE' (Let x e b) = do
        e' <- evaluateE e
        evaluateE $ sub b x e'
    evaluateE' (Case e ps) = do
        e' <- evaluateE e

        let candidates = catMaybes $ fmap sequence . fmap T.swap $ (\((p, b), e'') -> (matchPat mempty (p, e''), b)) <$> zip ps (repeat e')

        case candidates of
            []            -> traceShow (zip ps (repeat e'), (\((p, b), e'') -> (matchPat mempty (p, e''), b)) <$> zip ps (repeat e')) $ fail "Can't pattern match."
            (e'', m') : _ -> evaluateE $ foldl (\b (k, v) -> sub b k v) e'' (M.toList m')
    evaluateE' i@I{}          = pure i
    evaluateE' b@B{}          = pure b
    evaluateE' v@Var{}        = pure v
    evaluateE' l@Lam{}        = pure l
    evaluateE' (C c s)        = C c <$> mapM evaluateE s
    evaluateE' (Binop op l r) = do
        I l <- evaluateE l
        I r <- evaluateE r

        case op of
            "+"  -> pure $ I $ l + r
            "-"  -> pure $ I $ l - r
            "*"  -> pure $ I $ l * r
            "<"  -> pure $ B $ l < r
            "<=" -> pure $ B $ l <= r
            ">"  -> pure $ B $ l > r
            ">=" -> pure $ B $ l >= r

testEval :: Bool
testEval = R.runReader (evaluateE $ sub prg "m" (I 4)) (M.fromList defs) == I 30
  where
    Prg defs prg = testPrg

testPrg :: Prg
testPrg = Prg defs prg
  where
    prg = App (App (Func "sum") (App (Func "square") (App (App (Func "upto") (I 1)) (Var "m")))) (I 0)

    defs = [sumD, squareD, uptoD]

    sumD = ("sum", Lam "xs" $ Lam "a" $
                    Case (Var "xs")
                        [ (CPat "Nil" [], Var "a")
                        , (CPat "Cons" [VarPat "x", VarPat "xs"], Binop "+" (Var "x") (App (App (Func "sum") (Var "xs")) (Var "a")))
                        ])

    squareD = ("square", Lam "xs" $
                            Case (Var "xs")
                                [ (CPat "Nil" [], C "Nil" [])
                                , (CPat "Cons" [VarPat "x", VarPat "xs"], C "Cons" [Binop "*" (Var "x") (Var "x"), App (Func "square") (Var "xs")])
                                ])

    uptoD = ("upto", Lam "m" $ Lam "n" $
                            Case (Binop ">" (Var "m") (Var "n"))
                                [ (BPat True, C "Nil" [])
                                , (BPat False, C "Cons" [Var "m", App (App (Func "upto") (Binop "+" (Var "m") (I 1))) (Var "n")])
                                ])
