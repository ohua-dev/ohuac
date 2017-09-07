{-# LANGUAGE CPP, LambdaCase, OverloadedStrings, OverloadedLists, FlexibleContexts, TypeFamilies #-}
module Main where


import System.Environment
import System.Directory
import qualified Data.ByteString.Lazy as L
import Ohua.ALang.NS
import Ohua.ALang.Lang
import Data.IORef
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Ohua.Types
import Control.Concurrent.Async
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import qualified Data.Text as T
import Data.String (fromString)
import Data.Maybe
import Control.Monad
import System.FilePath ((<.>), takeExtension)
import Data.Monoid
import Control.Monad.Reader
import Control.Monad.RWS
import Data.Aeson
import Ohua.Serialize.JSON
import Data.Hashable
import Ohua.Compile
import Data.Foldable
import Control.Arrow
import Data.List (partition)

#ifdef WITH_SEXPR_PARSER
import qualified Ohua.Compat.SExpr.Lexer as SLex
import qualified Ohua.Compat.SExpr.Parser as SParse
#endif
#ifdef WITH_CLIKE_PARSER
import qualified Ohua.Compat.Clike.Lexer as CLex
import qualified Ohua.Compat.Clike.Parser as CParse
#endif


getParser :: String -> L.ByteString -> Namespace Binding
#ifdef WITH_SEXPR_PARSER
getParser ".ohuas" = SParse.parseNS . SLex.tokenize
#endif
#ifdef WITH_CLIKE_PARSER
getParser ".ohuac" = CParse.parseNS . CLex.tokenize
#endif
getParser ext = error $ "No parser defined for files with extension '" ++ ext ++ "'"


type IFaceDefs = HS.HashSet Binding
type ModMap = HM.HashMap Binding (MVar (Namespace ResolvedSymbol))
type ModTracker = IORef ModMap

resolveNS :: IFaceDefs -> Namespace Binding -> Namespace ResolvedSymbol
resolveNS ifacem ns@(Namespace modname algoImports sfImports decls main) = 
    ns { nsDecls = resDecls, nsMain = resMain }
  where
    (resDecls, resMain) = flip runReader (HS.fromMap $ HM.map (const ()) decls) $ (,) <$> traverse go decls <*> (case main of Nothing -> return Nothing; Just a -> Just <$> go a)

    go (Let assign val body) = 
        local (HS.union $ HS.fromList $ flattenAssign assign) $ Let assign <$> go val <*> go body
    go (Var bnd) = do
        isLocal <- asks (HS.member bnd)
        return $ Var $ 
            if isLocal then
                Local bnd
            else 
                case (HM.lookup bnd algoRefers, HM.lookup bnd sfRefers) of
                    (Just algo, Just sf) -> error $ "Ambiguous ocurrence of unqualified binding " ++ show bnd ++ ". Could refer to algo " ++ show algo ++ " or sf " ++ show sf
                    (Just algo, _) | HS.member algo ifacem -> Local algo
                    (_, Just sf) -> Sf (fnNameFromBinding sf) Nothing
                    _ -> Sf (fnNameFromBinding bnd) Nothing
    go (Apply expr expr2) = Apply <$> go expr <*> go expr2
    go (Lambda assign body) = 
        local (HS.union $ HS.fromList $ flattenAssign assign) $ Lambda assign <$> go body

    algoRefers = mkReferMap algoImports
    sfRefers = mkReferMap sfImports

    mkReferMap importList = HM.fromListWith reportCollidingRef
        [ (shortname, sourceNS <> "/" <> shortname)
        | (sourceNS, referList) <- importList
        , shortname <- referList
        ]

    fnNameFromBinding = FnName . unBinding
    reportCollidingRef a b = error $ "colliding refer for '" ++ show a ++ "' and '" ++ show b ++ "'"


readAndParse :: String -> IO (Namespace Binding)
readAndParse filename = getParser (takeExtension filename) <$> L.readFile filename


gatherDeps :: IORef ModMap -> Namespace a -> IO IFaceDefs
gatherDeps tracker Namespace{ nsAlgoImports=algoImports } = do
    mods <- mapConcurrently (registerAndLoad tracker) (map fst algoImports)
    return $ HS.fromList
        [ nsName ns <> "/" <> name
        | ns <- mods
        , name <- HM.keys $ nsDecls ns
        ]


findSourceFile :: Binding -> IO String
findSourceFile modname = do
    candidates <- filterM doesFileExist $ map (asFile <.>) extensions
    case candidates of
        [] -> error $ "No file found for module " ++ show modname
        [f] -> return f
        files -> error $ "Found multiple files matching " ++ show modname ++ ": " ++ show files
  where
    asFile = map (\case '.' -> '/'; a -> a) $ T.unpack $ unBinding modname
    extensions =
#ifdef WITH_SEXPR_PARSER
        ".ohuas" : 
#endif
#ifdef WITH_CLIKE_PARSER
        ".ohuac" :
#endif
        []


loadModule :: ModTracker -> Binding -> IO (Namespace ResolvedSymbol)
loadModule tracker modname = do
    filename <- findSourceFile modname
    rawMod <- readAndParse filename
    unless (nsName rawMod == modname) $ error $ "Expected module with name " ++ show modname ++ " but got " ++ show (nsName rawMod)
    deps <- gatherDeps tracker rawMod
    return $ resolveNS deps rawMod


registerAndLoad :: ModTracker -> Binding -> IO (Namespace ResolvedSymbol)
registerAndLoad tracker mod = do
    newModRef <- newEmptyMVar 
    actualRef <- atomicModifyIORef' tracker $ \map ->
        case HM.lookup mod map of
            Just mvar -> (map, Left mvar)
            Nothing -> (HM.insert mod newModRef map, Right newModRef)
    case actualRef of
        Left toWait -> readMVar toWait
        Right build -> do 
            compiled <- loadModule tracker mod
            putMVar build compiled
            return compiled


topSortMods :: [Namespace ResolvedSymbol] -> [Namespace ResolvedSymbol]
topSortMods = topSortWith nsName (map fst . nsAlgoImports)


topSortWith :: (Hashable b, Eq b) => (a -> b) -> (a -> [b]) -> [a] -> [a]
topSortWith getIdent getDeps mods' = snd $ evalRWS go (mempty, mods') ()
  where
    go = do
        (satisfied, avail) <- ask
        let (newSat, newAvail) = partition (all (`HS.member` satisfied) . getDeps) avail
        tell newSat
        local (HS.union (HS.fromList $ map getIdent newSat) *** const newAvail) go


topSortDecls :: [(Binding, Expression)] -> [(Binding, Expression)]
topSortDecls decls = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = HS.fromList $ map fst decls
    getDeps e = HS.toList $ snd $ evalRWS (go e) mempty ()
      where
        go (Let assign val body) = local (HS.union $ HS.fromList $ flattenAssign assign) $ go val >> go body
        go (Var (Local bnd)) = do
            isLocal <- asks (HS.member bnd)
            if isLocal then
                return ()
            else 
                when (bnd `HS.member` localAlgos) $ tell [bnd]
        go (Lambda assign body) = local (HS.union $ HS.fromList $ flattenAssign assign) $ go body
        go (Apply function val) = go function >> go val
                
    declsWDeps = zip decls $ map (getDeps . snd) decls

toLetExpr :: [Namespace ResolvedSymbol] -> Expression -> Expression
toLetExpr = foldl' go id
  where
    go f ns = foldl' go0 f decls
      where
        decls = topSortDecls $ HM.toList (nsDecls ns)
    
    go0 f (name, expr) = Let (Direct name) expr . f 


main :: IO ()
main = do
    [inputModStr] <- getArgs
    let inputMod = fromString inputModStr
    
    modTracker <- newIORef HM.empty

    mainMod <- registerAndLoad modTracker inputMod

    case nsMain mainMod of 
        Nothing -> error "Main module has no main function"
        Just expr -> do

            allMods <- mapM readMVar . HM.elems =<< readIORef modTracker

            let sorted = topSortMods allMods
            let asExpr = toLetExpr sorted expr
            
            let gr = either (error . T.unpack) id $ compile asExpr

            L.writeFile (inputModStr <.> "ohuao") $ encode gr

