module Supercompiler where

import           Control.Monad
import           Control.Monad.Reader (Reader)
import qualified Control.Monad.Reader as R
import           Control.Monad.State  (State)
import qualified Control.Monad.State  as ST
import           Data.Bifunctor       (first, second)
import qualified Data.Either          as E
import qualified Data.List            as L
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as M
import           Data.Maybe           (catMaybes)
import           Data.Semigroup       ((<>))
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

-- evalStep :: E -> DefsM -> Maybe E
-- evalStep e defs = evaluateE' e
--   where
--     evaluateE' :: E -> Maybe E
--     evaluateE' (Func x)          = Just $ defs M.! x
--     evaluateE' (App (Lam x b) r) = Just $ sub b x r
--     evaluateE' (App l r)         =
--         case evalStep l defs of
--             Nothing -> fmap (App l) $ evalStep e defs
--             Just l' -> Just $ App l' r
--     evaluateE' (Let x e b) =
--       case evalStep e  defs of
--         Nothing -> Just $ sub b x e
--         Just e' -> Just $ Let x e' b
--     evaluateE' (Case e ps) =
--       case evalStep e defs of
--         Nothing -> do
--           let candidates = catMaybes $ fmap sequence . fmap T.swap $ (\((p, b), e'') -> (matchPat mempty (p, e''), b)) <$> zip ps (repeat e)
--           case candidates of
--               []            -> fail "Can't pattern match."
--               (e'', m') : _ -> evalStep (foldl (\b (k, v) -> sub b k v) e'' (M.toList m')) defs
--         Just e' -> Just $ Case e' ps
--     evaluateE' i@I{}          = pure i
--     evaluateE' b@B{}          = pure b
--     evaluateE' v@Var{}        = pure v
--     evaluateE' l@Lam{}        = pure l
--     evaluateE' (C c s)        = C c <$> mapM evaluateE s
--     evaluateE' (Binop op l r) = do
--         I l <- evaluateE l
--         I r <- evaluateE r

--         case op of
--             "+"  -> pure $ I $ l + r
--             "-"  -> pure $ I $ l - r
--             "*"  -> pure $ I $ l * r
--             "<"  -> pure $ B $ l < r
--             "<=" -> pure $ B $ l <= r
--             ">"  -> pure $ B $ l > r
--             ">=" -> pure $ B $ l >= r

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
            []            -> fail "Can't pattern match."
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

---------------------------------------------------------------
-- Supercompiler.
---------------------------------------------------------------

---------------------------------------------------------------
-- Homeomorphic inclusion for E.
---------------------------------------------------------------

isHomeomorphicInclusion :: E -> E -> Bool
-- isHomeomorphicInclusion expr expr' = traceShow (expr, expr', isHomeomorphicInclusion' expr expr') $ isHomeomorphicInclusion' expr expr'
isHomeomorphicInclusion expr expr' = diving expr expr' || coupling expr expr'
  where
    diving :: E -> E -> Bool
    diving e (App l r)     = isHomeomorphicInclusion e l || isHomeomorphicInclusion e r
    diving e (Case e' ps)  = isHomeomorphicInclusion e e' || any (isHomeomorphicInclusion e . snd) ps
    diving e (Let _ e' b)  = isHomeomorphicInclusion e e' || isHomeomorphicInclusion e b
    diving e (Lam _ b)     = isHomeomorphicInclusion e b
    diving e (Binop _ l r) = isHomeomorphicInclusion e l || isHomeomorphicInclusion e r
    diving e (C _ s)       = any (isHomeomorphicInclusion e) s
    diving e e'            = e == e'

    coupling :: E -> E -> Bool
    coupling (App l r) (App l' r')            = isHomeomorphicInclusion l l' && isHomeomorphicInclusion r r'
    coupling (Case e ps) (Case e' ps')        = isHomeomorphicInclusion e e' && hasMapping
      where
        permutations' = L.permutations ps'
        allMappings   = concatMap (allLinearMappings ps) permutations'

        hasMapping = any (all (\((p, ex), (p', ex')) -> p == p' && isHomeomorphicInclusion ex ex')) allMappings

        allLinearMappings :: [(Pat, E)] -> [(Pat, E)] -> [[((Pat, E), (Pat, E))]]
        allLinearMappings [] _ = []
        allLinearMappings _ [] = []
        allLinearMappings l@(x : xs) l'@(y : ys) | length l == length l' = pure $ zip l l'
                                                 | length l > length l'  = []
                                                 | otherwise           = first <> rest
          where
            first = ((x, y) :) <$> allLinearMappings xs ys
            rest  = allLinearMappings l ys
    coupling (Let _ e b) (Let _ e' b')        = isHomeomorphicInclusion e e' && isHomeomorphicInclusion b b'
    coupling (Lam _ b) (Lam _ b')             = isHomeomorphicInclusion b b' -- don't bother with order of lambdas
    coupling (Binop op l r) (Binop op' l' r') = op == op' && isHomeomorphicInclusion l l' && isHomeomorphicInclusion r r'
    coupling (C c s) (C c' s')                = c == c' && and (zipWith isHomeomorphicInclusion s s')
    coupling Var{} Var{}                      = True
    coupling e e'                             = e == e'

---------------------------------------------------------------
-- Most tight generalization.
---------------------------------------------------------------

type SubT = Either String E

type Sub = [(String, SubT)]
type Gen = (E, Sub, Sub)

unionSubs :: Sub -> Sub -> Sub
unionSubs s s' = foldl (\s'' (k, vE) ->
    case vE of
      Right v -> fmap (second $ fmap (\x -> sub x k v)) s''
      _       -> s'') s s' <> s'

unionSubsMany :: [Sub] -> Sub
unionSubsMany = foldl unionSubs []

applySub :: Sub -> E -> E
applySub _ f@(Func _)   = f
applySub s (App l r)    = App (applySub s l) (applySub s r)
applySub s (Case e ps)  = Case (applySub s e) (fmap (second $ applySub s) ps)
applySub s (Let x e e') = Let n (applySub s e) (applySub s e')
  where
    n = maybe x (\(Left n) -> n) $ L.lookup x s
applySub _ i@I{}     = i
applySub _ b@B{}     = b
applySub s (Var x)   = maybe (Var x) (\(Right x) -> x) $ L.lookup x s
applySub s (Lam x e) = Lam n $ applySub s e
  where
    n = maybe x (\(Left n) -> n) $ L.lookup x s
applySub s (Binop x l r) = Binop x (applySub s l) (applySub s r)
applySub s (C x xs)      = C x $ fmap (applySub s) xs

type NameGen = [String]

nameGen :: NameGen
nameGen = fmap (\x -> "x" <> show x) [0..]

freshName :: State NameGen String
freshName = do
    (x : xs) <- ST.get
    ST.modify (const xs)
    pure x

mtg :: E -> E -> State NameGen Gen
mtg (App l r) (App l' r') = do
    (el, sl, sl') <- mtg l l'
    (er, sr, sr') <- mtg r r'

    pure (App el er, sl `unionSubs` sr, sl' `unionSubs` sr')
mtg (Case e ps) (Case e' ps') = do
    (ee, se, se') <- mtg e e'

    when (fmap fst ps /= fmap fst ps') $ fail "Different patterns in mtg."

    (eps, sps, sps') <- unzip3 <$> zipWithM mtg (fmap snd ps) (fmap snd ps')
    pure (Case ee (zip (fmap fst ps) eps), unionSubsMany (se : sps), unionSubsMany (se' : sps'))
mtg (Let x e b) (Let x' e' b') = do
    (ee, se, se') <- mtg e e'
    (eb, sb, sb') <- mtg b b'
    n             <- freshName

    pure (Let n ee eb, unionSubsMany [[(n, Left x)], se, sb], unionSubsMany [[(n, Left x')], se', sb'])
mtg (Lam x b) (Lam x' b') = do
    (eb, sb, sb') <- mtg b b'
    n             <- freshName

    pure (Lam n eb, unionSubsMany [[(n, Left x)], sb], unionSubsMany [[(n, Left x')], sb'])
mtg (Binop op l r) (Binop op' l' r') = do
    when (op /= op') $ fail "Can't find mtg of binops."

    (el, sl, sl') <- mtg l l'
    (er, sr, sr') <- mtg r r'

    pure (Binop op el er, sl `unionSubs` sr, sl' `unionSubs` sr')
mtg (C c s) (C c' s') = do
    when (c /= c' || length s /= length s') $ fail "Can't find mtg of constructors."

    (es, ss, ss') <- unzip3 <$> zipWithM mtg s s'

    pure (C c es, unionSubsMany ss, unionSubsMany ss')
mtg x (Var n) =
    pure (Var n, [(n, Right x)], [])
mtg x y =
    if x == y
      then pure (x, [], [])
      else do
        n <- freshName
        pure (Var n, [(n, Right x)], [(n, Right y)])

mtgRun :: State NameGen Gen -> Gen
mtgRun = flip ST.evalState nameGen

data Label = AppL
           | ArgNumL Int
           | IntL Int
           | BoolL Bool
           | ConsL
           | CaseL
           | LetL

data Tree = Node E [(Label, Tree)] | Leaf

buildTree :: E -> State Tree (Maybe E)
buildTree = undefined

---------------------------------------------------------------
-- Tests.
---------------------------------------------------------------

runTests :: IO ()
runTests = do
    putStrLn "Running interpreter test."
    pure testEval

    putStrLn "Running homeomorphic inclusion test."
    pure homeomorphicInclusionTest

    putStrLn "Running mtg test."
    pure mtgTest

    pure ()

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
                        , (CPat "Cons" [VarPat "x", VarPat "xs"], (App (App (Func "sum") (Var "xs")) (Binop "+" (Var "a") (Var "xs"))))
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

homeomorphicInclusionTest :: Bool
homeomorphicInclusionTest = isHomeomorphicInclusion e e' && isHomeomorphicInclusion e e'' == False
  where
    e = Lam "xs" $
            Case (Var "xs")
                [ (CPat "Nil" [], C "Nil" [])
                , (CPat "Cons" [VarPat "x", VarPat "xs"], C "Cons" [Binop "*" (Var "x") (Var "x"), App (Func "square") (Var "xs")])
                ]

    e' = Lam "ys" $ Lam "xs" $
            Case (Var "xs")
                [ (CPat "Nil" [], C "Cons" [Binop "+" (Var "ys") (I 32), C "Nil" []])
                , (CPat "Cons" [VarPat "x", VarPat "xs", VarPat "aaaa"], I 42)
                , (CPat "Cons" [VarPat "x", VarPat "xs"], C "Cons" [B True, C "Cons" [Binop "+" (Binop "*" (Var "x") (Var "x")) (Var "ys"), App (Lam "x" (Var "x")) (App (Func "square") (Var "xs"))]])
                , (CPat "Cons" [VarPat "x", VarPat "xs", VarPat "aaaaaaaa", VarPat "ee"], I 42)
                ]

    e'' = Lam "ys" $ Lam "xs" $
        Case (Var "xs")
            [ (CPat "Nil" [], C "Cons" [Binop "+" (Var "ys") (I 32), C "Nil" []])
            , (CPat "Cons" [VarPat "x", VarPat "xs", VarPat "aaaa"], I 42)
            , (CPat "Cons" [VarPat "x", VarPat "xs"], C "Cons" [B True, C "Cons" [Binop "+" (Binop "*" (Var "x") (I 21)) (Var "ys"), App (Lam "x" (Var "x")) (App (Func "square") (Var "xs"))]])
            , (CPat "Cons" [VarPat "x", VarPat "xs", VarPat "aaaaaaaa", VarPat "ee"], I 42)
            ]

mtgTest :: Bool
mtgTest = test1 && test2 && test3 && test4
  where
    app1 = App (Var "a") (I 42)
    app2 = App (I 21) (I 42)

    (mtg1@(App Var{} Var{}), s1, s2) = mtgRun $ mtg app1 app2
    test1 = applySub s1 mtg1 == app1 && applySub s2 mtg1 == app2

    case1 = Case app1 [ (VarPat "x", Binop "+" (App app1 app2) (I 31))
                      , (VarPat "y", Binop "-" (App app1 app1) (App (App app2 app1) app1))
                      ]
    case2 = Case app2 [ (VarPat "x", Binop "+" (App app2 app2) (Var "t"))
                      , (VarPat "y", Binop "-" (App app1 (I 31)) (App (Var "z") app1))
                      ]

    (mtg2@(Case (App Var{} Var{}) [ (VarPat "x", Binop "+" (App (App Var{} Var{}) (App Var{} Var{})) Var{})
                                  , (VarPat "y", Binop "-" (App (App Var{} Var{}) Var{}) (App Var{} (App Var{} Var{})))
                                  ]), s1', s2') = mtgRun $ mtg case1 case2

    test2 = applySub s1' mtg2 == case1 && applySub s2' mtg2 == case2

    lam1 = Lam "x" $ Lam "y" $ Lam "z" $ App case1 (Var "z")
    lam2 = Lam "x1" $ Lam "y1" $ Lam "z1" $ App case2 (I 31)
    lam3 = Lam "x" $ Lam "z" $ App case1 (Var "z")

    (mtg3@(Lam _ (Lam _ (Lam _ (App (Case (App Var{} Var{}) [ (VarPat "x", Binop "+" (App (App Var{} Var{}) (App Var{} Var{})) Var{})
                                                               , (VarPat "y", Binop "-" (App (App Var{} Var{}) Var{}) (App Var{} (App Var{} Var{})))
                                                               ]) Var{})))), s1'', s2'') = mtgRun $ mtg lam1 lam2

    test3 = applySub s1'' mtg3 == lam1 && applySub s2'' mtg3 == lam2

    (mtg4@(Lam _ (Lam _ Var{})), s11, s22) = mtgRun $ mtg lam1 lam3

    test4 = applySub s11 mtg4 == lam1 && applySub s22 mtg4 == lam3

-- 1. Новую вершину в дерево добавляем перед анфолдингом функции.
-- 2. Чтобы восстанавливать выражение, лучше завести тип Контекст, в который можно будет встроить текущее выражение.
--    Контекст, наверное, должен повторять по структуре сами выражния. Отдельно надо обособить Дырку в этом Контксте.
