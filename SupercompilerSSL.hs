{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SupercompilerSSL where

import           Control.Monad
import           Data.Function  (on)
import           Data.List
import           Data.Maybe
import           Data.Semigroup ((<>))
import           Data.Tuple     (swap)

import           Debug.Trace    (traceShow)

--------------------------------------------------------------
-- Language.
--------------------------------------------------------------

type Name = String

data E = Var Name
       | C Name [E]
       | FCall Name [E]
       | GCall Name [E]
       | Let Name E E
  deriving (Eq, Show)

data Pat = Pat Name [Name]
  deriving (Eq, Show)

data Def = FDef Name [Name] E
         | GDef Name Pat [Name] E
  deriving (Eq, Show)

data Prg = Prg [Def] E
  deriving (Eq, Show)

--------------------------------------------------------------
-- Aux.
--------------------------------------------------------------

type Renaming = [(Name, Name)]
type Subst = [(Name, E)]
type Env = [(Name, E)]

freshVars :: [Name]
freshVars = fmap (("v" <>) . show) [0 ..]

--------------------------------------------------------------
-- Graph.
--------------------------------------------------------------

data Step a = Trans a
            | Stop
            | Decompose [a]
            | Variants [((Name, Pat), a)]
            | Fold Renaming a
  deriving (Eq, Show)

instance Functor Step where
    fmap f (Trans a)     = Trans $ f a
    fmap _ Stop          = Stop
    fmap f (Decompose l) = Decompose $ fmap f l
    fmap f (Variants l)  = Variants $ fmap (fmap f) l
    fmap f (Fold r a)    = Fold r $ f a

data Graph a = Node a (Step (Graph a))

instance Show a => Show (Graph a) where
    show :: forall a. Show a => Graph a -> String
    show = showWithIndent ""
      where
        showWithIndent :: String -> Graph a -> String
        showWithIndent indent (Node e n) = indent <> show e <> " " <>
          case n of
            Trans n'           -> "=> \n" <> showWithIndent nextIndent n'
            Stop               -> "STOP\n"
            Decompose l        -> intercalate thisIndent $ fmap (("-> \n" <>) . showWithIndent nextIndent) l
            Variants l         -> intercalate thisIndent $ fmap (\(p, x) -> ("--" <> show p <> "--> \n") <> showWithIndent nextIndent x) l
            Fold r (Node e' _) -> "= folding with " <> show r <> " to " <> show e' <> "\n"
          where
            nextIndent = "  " <> indent
            thisIndent = indent <> replicate (length (show e) + 1) ' '

--------------------------------------------------------------
-- Utilities.
--------------------------------------------------------------

findFDef :: [Def] -> Name -> Def
findFDef [] name                         = error $ "No f-function with name: " <> name
findFDef (def@(FDef name' _ _) : _) name | name == name' = def
findFDef (_ : xs) name                   = findFDef xs name

findGDefs :: [Def] -> Name -> [Def]
findGDefs [] name                            = []
findGDefs (def@(GDef name' _ _ _) : xs) name | name == name' = def : findGDefs xs name
findGDefs (_ : xs) name                      = findGDefs xs name

findGDefForPat :: [Def] -> Name -> Name -> Def
findGDefForPat defs name patName = maybe err id $ find patMatcher $ findGDefs defs name
  where
    patMatcher :: Def -> Bool
    patMatcher (GDef _ (Pat patName' _) _ _) = patName' == patName
    patMatcher _                             = err

    err = error $ "Can't find def for g-function " <> name <> " with pat name " <> patName

sub :: Subst -> E -> E
sub subst (Var x)        = maybe (Var x) id $ x `lookup` subst
sub subst (C n args)     = C n $ fmap (sub subst) args
sub subst (FCall n args) = FCall n $ fmap (sub subst) args
sub subst (GCall n args) = GCall n $ fmap (sub subst) args
sub subst (Let n e e')   = Let n (sub subst e) (sub subst e')

unusedNames :: [Name] -> [Name] -> [Name]
unusedNames = (\\)

usedNames :: E -> [Name]
usedNames = nub . usedNames'
  where
    usedNames' :: E -> [Name]
    usedNames' (Var x)        = [x]
    usedNames' (C _ args)     = concatMap usedNames args
    usedNames' (FCall _ args) = concatMap usedNames args
    usedNames' (GCall _ args) = concatMap usedNames args
    usedNames' (Let _ e e')   = usedNames e <> usedNames e'

isVar :: E -> Bool
isVar Var{} = True
isVar _     = False

isCall :: E -> Bool
isCall FCall{} = True
isCall GCall{} = True
isCall _       = False

findRenaming :: E -> E -> Maybe Renaming
findRenaming from to = join . fmap getBijection . helper from $ to
  where
    getBijection :: Renaming -> Maybe Renaming
    getBijection r | injection && surjection && sizesEq = Just nubbed
                   | otherwise                          = Nothing
      where
        nubbed = nub r

        injection  = (length . groupBy ((==) `on` snd) . sortOn snd $ nubbed) == length nubbed
        surjection = True
        sizesEq    = length (nub $ fmap fst nubbed) == length (nub $ fmap snd nubbed)

    helper :: E -> E -> Maybe Renaming
    helper (Var x) (Var x')                = Just [(x, x')]
    helper (C n args) (C n' args')         = findRenamingConsts (n, args) (n', args')
    helper (FCall n args) (FCall n' args') = findRenamingConsts (n, args) (n', args')
    helper (GCall n args) (GCall n' args') = findRenamingConsts (n, args) (n', args')
    helper (Let n e b) (Let n' e' b')      = (<>) <$> helper e e' <*> helper b (sub [(n, Var n')] b')
    helper _ _                             = Nothing

    findRenamingConsts :: (Name, [E]) -> (Name, [E]) -> Maybe Renaming
    findRenamingConsts (n, es) (n', es') | n == n' && length es == length es' = concat <$> zipWithM helper es es'
                                         | otherwise = Nothing

--------------------------------------------------------------
-- Whistles.
--------------------------------------------------------------

class IsWhistle a where
    whistle :: [E] -> E -> Bool

data SizeWhistle = SizeWhistle
  deriving (Eq, Show)

eSize :: E -> Int
eSize (Var _)        = 1
eSize (C _ args)     = 1 + sum (fmap eSize args)
eSize (FCall _ args) = 1 + sum (map eSize args)
eSize (GCall _ args) = 1 + sum (fmap eSize args)
eSize (Let _ e e')   = 1 + eSize e + eSize e'

sizeWhistleBound :: Int
sizeWhistleBound = 40

instance IsWhistle SizeWhistle where
    whistle _ e@(FCall _ args) = not (all isVar args) && eSize e > sizeWhistleBound
    whistle _ e@(GCall _ args) = not (all isVar args) && eSize e > sizeWhistleBound
    whistle _ _                = False

--------------------------------------------------------------
-- Semantics.
--------------------------------------------------------------

interpret :: Prg -> E
interpret (Prg defs e) = helper e
  where
    helper :: E -> E
    helper (Var x)        = Var x
    helper (C n args)     = C n $ fmap helper args
    helper (FCall n args) = helper $ sub (zip args' args) b
      where
        FDef _ args' b = findFDef defs n
    helper (GCall n (C n' args1 : args2)) = helper $ sub (zip (args1' <> args2') (args1 <> args2)) b
      where
        GDef _ (Pat _ args1') args2' b = findGDefForPat defs n n'
    helper (GCall n (x : xs)) = helper (GCall n $ helper x : xs)
    helper (Let n e b)   = helper $ sub [(n, e)] b
    helper e             = error $ "Can't evaluate expression: " <> show e

addZ :: Def
addZ = GDef "add" (Pat "Z" []) ["y"] $ Var "y"

addS :: Def
addS = GDef "add" (Pat "S" ["x"]) ["y"] $ C "S" [GCall "add" [Var "x", Var "y"]]

multZ :: Def
multZ = GDef "mult" (Pat "Z" []) ["y"] $ C "Z" []

multS :: Def
multS = GDef "mult" (Pat "S" ["x"]) ["y"] $ GCall "add" [Var "y", GCall "mult" [Var "x", Var "y"]]

sqr :: Def
sqr = FDef "sqr" ["x"] $ GCall "mult" [Var "x", Var "x"]

evenZ :: Def
evenZ = GDef "even" (Pat "Z" []) [] $ C "True" []

evenS :: Def
evenS = GDef "even" (Pat "S" ["x"]) [] $ GCall "odd" [Var "x"]

oddZ :: Def
oddZ = GDef "odd" (Pat "Z" []) [] $ C "False" []

oddS :: Def
oddS = GDef "odd" (Pat "S" ["x"]) [] $ GCall "even" [Var "x"]

defs :: [Def]
defs = [addZ, addS, multZ, multS, sqr, evenZ, evenS, oddZ, oddS]

z = C "Z" []
s = C "S" . pure

three = s $ s $ s $ z
nine  = s $ s $ s $ s $ s $ s $ s $ s $ s $ z
true  = C "True" []
false = C "False" []

interpretTest :: Bool
interpretTest = sqrTest && isOddTest
  where

    sqrTest   = interpret (Prg defs (FCall "sqr" [three])) == nine
    isOddTest = interpret (Prg defs (GCall "odd" [FCall "sqr" [three]])) == true

--------------------------------------------------------------
-- Driving.
--------------------------------------------------------------

drive :: Prg -> [Name] -> Step E
drive (Prg defs e) = helper e
  where
    helper :: E -> [Name] -> Step E
    helper Var{} _          = Stop
    helper (C _ []) _       = Stop
    helper (C _ args) _     = Decompose args
    helper (Let _ e b) _    = Decompose [e, b]
    helper (FCall n args) _ = Trans $ sub (zip args' args) b
      where
        FDef _ args' b = findFDef defs n
    helper (GCall n (C n' args1 : args2)) _ = Trans $ sub (zip (args1' <> args2') (args1 <> args2)) b
      where
        GDef _ (Pat _ args1') args2' b = findGDefForPat defs n n'
    helper (GCall n (Var x : args)) ns = Variants $ getVariants (findGDefs defs n) x args ns
    helper (GCall n (x : xs))       ns = fmap (GCall n . flip (:) xs) $ helper x ns

    getVariants :: [Def] -> Name -> [E] -> [Name] -> [((Name, Pat), E)]
    getVariants defs n args ns = fmap (getVariant ns n args) defs

    getVariant :: [Name] -> Name -> [E] -> Def -> ((Name, Pat), E)
    getVariant ns n args (GDef _ (Pat nP argsP) args' b) = res
      where
        fresh = take (length argsP) ns
        res   = ((n, Pat nP fresh), sub (zip (argsP <> args') (fmap Var fresh <> args)) b)
    getVariant _ _ _ _                                   = error "getVariant for non-g-function def."

buildProcessTree :: Prg -> Graph E
buildProcessTree (Prg defs expr) = helper expr freshVars
  where
    helper :: E -> [Name] -> Graph E
    helper e ns = res
      where
        driven = drive (Prg defs e) ns

        res = Node e $
          case driven of
              Stop         -> Stop
              Decompose es -> Decompose $ fmap (flip helper ns) es
              Trans e      -> Trans $ helper e ns
              Variants l   -> Variants $ fmap (\(p@(n, Pat _ ns'), x) -> (p, helper x $ ns `unusedNames` ns')) l

driveTest :: Bool
driveTest = transTest && variantsTest
  where
    transTest =
      drive (Prg defs (GCall "odd" [FCall "sqr" [Var "x"]])) freshVars ==
        Trans (GCall "odd" [GCall "mult" [Var "x",Var "x"]])

    variantsTest =
      drive (Prg defs (GCall "odd" [GCall "mult" [Var "x",Var "x"]])) freshVars ==
        Variants [(("x",Pat "Z" []),GCall "odd" [C "Z" []]),(("x",Pat "S" ["v0"]),GCall "odd" [GCall "add" [Var "x",GCall "mult" [Var "v0",Var "x"]]])]

--------------------------------------------------------------
-- Folding.
--------------------------------------------------------------

foldTree :: Graph E -> Graph E
foldTree = foldFurther (performFolding [])
  where
    foldFurther :: (Graph E -> Graph E -> Graph E) -> Graph E -> Graph E
    foldFurther f (Node e next) =
      case next of
        Stop        -> Node e Stop
        Decompose l -> let next' = Node e $ Decompose $ fmap (f next') l in next'
        Variants l  -> let next' = Node e $ Variants $ fmap (fmap $ f next') l in next'
        Trans n     -> let next' = Node e $ Trans $ f next' n in next'
        Fold r n    -> Node e $ Fold r n

    performFolding :: [Graph E] -> Graph E -> Graph E -> Graph E
    performFolding toRoot prev cur@(Node e _) | isCall e, Just (r, n) <- getRenaming pathToRoot e = Node e (Fold r n)
                                              | otherwise = foldFurther (performFolding pathToRoot) cur
      where
        pathToRoot = prev : toRoot

    getRenaming :: [Graph E] -> E -> Maybe (Renaming, Graph E)
    getRenaming nodes e = listToMaybe $ catMaybes $ fmap (\x@(Node e' _) -> swap <$> sequence (x, findRenaming e e')) nodes

testTree :: Graph E
testTree = buildProcessTree $ Prg defs $ GCall "odd" [FCall "sqr" [Var "x"]]
