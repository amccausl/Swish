> {-# OPTIONS -fglasgow-exts #-}
> {-# LANGUAGE UndecidableInstances #-}

> module Swish.HaskellRDF.Dfa.Dfa (
>     Re(..),
>     matchRe,
>     matchRe2
> ) where

> import Control.Monad.Identity
> import Control.Monad.Reader
> import Control.Monad.State
> import qualified Data.List as L
> import qualified Data.Map as M
> import qualified Data.Array as A
> import Data.Maybe

import IOExts


The type of a regular expression.

> data Re t
>   = ReOr [Re t]
>   | ReCat [Re t]
>   | ReStar (Re t)
>   | RePlus (Re t)
>   | ReOpt (Re t)
>   | ReTerm [t]
>       deriving (Show)


The internal type of a regular expression.

> type SimplRe t = Int
> data SimplRe' t
>   = SReOr (SimplRe t) (SimplRe t)
>   | SReCat (SimplRe t) (SimplRe t)
>   | SReStar (SimplRe t)
>   | SReLambda
>   | SReNullSet
>   | SReTerm t
>       deriving (Eq, Ord, Show)


The regular expression builder monad.

> data (Ord t) => ReRead t
>  = ReRead {
>       rerNullSet      :: SimplRe t,
>       rerLambda       :: SimplRe t
>  }

> data (Ord t) => ReState t
>   = ReState {
>       resFwdMap       :: M.Map (SimplRe t) (ReInfo t),
>       resBwdMap       :: M.Map (SimplRe' t) (SimplRe t),
>       resNext         :: Int,
>       resQueue        :: ([SimplRe t], [SimplRe t]),
>       resStatesDone   :: [SimplRe t]
>     }

> type ReM m t a = StateT (ReState t) (ReaderT (ReRead t) m) a



Running the monad is tricky because the reader transformer (which
is the _inner_ transformer) requires information gained from
initialising the mutable state.  We could do some trickiness with
lazy evaluation, but it would be hard to get right.

What we do instead is run a "bootstrap" monad which does the
initialisation then returns the state.  Then we construct a new
monad using that initial state.  Simple but effective.  The only
thing to be careful about is to make sure that the bootstrap code
does not depend on the reader state.  As it happens, we only call
remInsert which only touches mutable state.


> remRun :: (ReVars m t) => ReM m t a -> m a
> remRun m
>  = do (inits, initr) <- runReaderT (evalStateT bootstrap initState) initRead
>       runReaderT (evalStateT m inits) initr
>  where
>       initState
>         = ReState {
>               resFwdMap = M.empty,
>               resBwdMap = M.empty,
>               resNext = 0,
>               resQueue = ([],[]),
>               resStatesDone = []
>         }
>       initRead
>         = ReRead { rerNullSet = undefined, rerLambda = undefined }
>       bootstrap
>          = do
>               nulli <- remInsert (reiMake SReNullSet False)
>               lami  <- remInsert (reiMake SReLambda  True)
>               s <- get
>               r <- ask
>               return (s, r { rerNullSet = nulli, rerLambda = lami })




Utility typeclasses for enforcing all the constraints we need
on our monad's free type variables.  Note that this requires both
-fglasgow-exts and -fallow-undecidable-instances in GHC to work
properly.

> class (Monad m, Ord t) => ReVars m t where { }
> instance (Monad m, Ord t) => ReVars m t where { }


Operations on the monad.

> remNullSet :: (ReVars m t) => ReM m t (SimplRe t)
> remNullSet = asks rerNullSet

> remLambda :: (ReVars m t) => ReM m t (SimplRe t)
> remLambda = asks rerLambda

> remStateDone :: (ReVars m t) => SimplRe t -> ReM m t ()
> remStateDone re
>   = do s <- get
>        put (s { resStatesDone = re:resStatesDone s })

> remPush :: (ReVars m t) => [SimplRe t] -> ReM m t ()
> remPush res
>   = do s <- get
>        let (qf,qb) = resQueue s
>        put (s { resQueue = (qf, res ++ qb) })

> remPop :: (ReVars m t) => ReM m t (Maybe (SimplRe t))
> remPop
>   = get >>= \s ->
>       let (qf,qb) = resQueue s
>       in
>           case qf of
>               (re:res) -> put (s { resQueue = (res,qb) }) >> return (Just re)
>               []       -> if null qb then return Nothing
>                           else put (s { resQueue = (reverse qb,[]) })
>                                       >> remPop



> remInsert :: (ReVars m t) => ReInfo t -> ReM m t (SimplRe t)
> remInsert reinfo
>   = do s <- get
>        let fwd = resFwdMap s
>            bwd = resBwdMap s
>            newre = resNext s
>        put (s { resFwdMap = M.insert newre reinfo fwd,         -- PROBLEM
>                resBwdMap = M.insert (reiSRE reinfo) newre bwd,
>                resNext = newre + 1 })
>        return newre


> remLookupFwd :: (ReVars m t) => SimplRe t -> ReM m t (ReInfo t)
> remLookupFwd re
>   = do fwd <- gets resFwdMap
>        let { Just reinfo = M.lookup re fwd }                    -- PROBLEM
>        return reinfo


> remLookupBwd :: (ReVars m t) => SimplRe' t
>       -> ReM m t (Maybe (SimplRe t))
> remLookupBwd re
>   = do bwd <- gets resBwdMap
>        return (M.lookup re bwd)                                -- PROBLEM


remAdd implements hash consing.  Given a SimplRe' in as close
to "canonical" form as possible, this tries to find a SimplRe
that matches (if possible), and otherwise constructs a new one.

> remAdd :: (ReVars m t) => SimplRe' t -> ReM m t (SimplRe t)
> remAdd sre
>   = remLookupBwd sre >>= \ maybere ->
>       case maybere of
>           Just re -> return re
>           Nothing -> doInsert
>   where
>       doInsert
>         = remNullable sre >>= \nullable ->
>               remInsert (reiMake sre nullable)


> remSetDfaState :: (ReVars m t) => SimplRe t -> ReDfaState t ->
>                       ReM m t (ReDfaState t)
> remSetDfaState re dfa
>   = do s <- get
>        let    Just reinfo = M.lookup re (resFwdMap s)              -- PROBLEM
>               reinfo' = reinfo { reiDfa = Just dfa }
>        put (s { resFwdMap = M.insert  re reinfo' (resFwdMap s) })    -- PROBLEM
>        return dfa


The ReInfo type

> data ReInfo t
>   = ReInfo {
>       reiSRE          :: SimplRe' t,
>       reiNullable     :: Bool,
>       reiDfa          :: Maybe (ReDfaState t)
>     }
>       deriving (Show)

> reiMake :: SimplRe' t -> Bool -> ReInfo t
> reiMake re nullable
>   = ReInfo { reiSRE = re, reiNullable = nullable, reiDfa = Nothing }


Regular expression builder.

> remNullable :: (ReVars m t) => SimplRe' t -> ReM m t Bool
> remNullable (SReOr e1 e2)
>   = do ei1 <- remLookupFwd e1
>        ei2 <- remLookupFwd e2
>        return $ reiNullable ei1 || reiNullable ei2
> remNullable (SReCat e1 e2)
>   = do ei1 <- remLookupFwd e1
>        ei2 <- remLookupFwd e2
>        return $ reiNullable ei1 && reiNullable ei2
> remNullable (SReStar _)
>   = return True
> remNullable SReLambda
>   = return True
> remNullable SReNullSet
>   = return False
> remNullable (SReTerm _)
>   = return False



> remBuildOne :: (ReVars m t) => SimplRe' t ->
>               ReM m t (SimplRe t)

> remBuildOne re@(SReOr e1 e2)
>   | e1 == e2   = return e1
>   | e1 > e2    = remBuildOne (SReOr e2 e1)
>   | otherwise
>       = do ei1 <- remLookupFwd e1
>            ei2 <- remLookupFwd e2
>            remBuildOr e1 e2 (reiSRE ei1) (reiSRE ei2)
>       where
>           remBuildOr _  e3 (SReOr e1 e2) _
>             = remBuildOne (SReOr e2 e3) >>= \ e2' ->
>               remBuildOne (SReOr e1 e2')
>           remBuildOr _  e2 SReNullSet _ = return e2
>           remBuildOr e1 _  _ SReNullSet = return e1
>           remBuildOr _  _  _ _ = remAdd re

> remBuildOne re@(SReCat e1 e2)
>   = do ei1 <- remLookupFwd e1
>        ei2 <- remLookupFwd e2
>        remBuildCat e1 e2 (reiSRE ei1) (reiSRE ei2)
>   where
>       remBuildCat _  e3 (SReCat e1 e2) _
>         = remBuildOne (SReCat e2 e3) >>= \ e2' ->
>           remBuildOne (SReCat e1 e2')
>       remBuildCat e1 _  SReNullSet _ = return e1
>       remBuildCat _  e2 SReLambda  _ = return e2
>       remBuildCat _  e2 _ SReNullSet = return e2
>       remBuildCat e1 _  _ SReLambda  = return e1
>       remBuildCat _  _  _ _ = remAdd re

> remBuildOne re@(SReStar e)
>   = do ei <- remLookupFwd e
>        remBuildStar e (reiSRE ei)
>   where
>       remBuildStar e (SReStar _) = return e
>       remBuildStar e SReLambda   = return e
>       remBuildStar e SReNullSet  = remLambda
>       remBuildStar _ _           = remAdd re

> remBuildOne re@SReLambda = remLambda

> remBuildOne re@SReNullSet = remNullSet

> remBuildOne re@(SReTerm t) = remAdd re



> remBuild :: (ReVars m t) => Re t -> ReM m t (SimplRe t)
> remBuild (ReOr [])
>   = remNullSet
> remBuild (ReOr [e])
>   = remBuild e
> remBuild (ReOr (e:es))
>   = do es' <- remBuild (ReOr es)
>        e'  <- remBuild e
>        remBuildOne (SReOr e' es')
> remBuild (ReCat [])
>   = remLambda
> remBuild (ReCat [e])
>   = remBuild e
> remBuild (ReCat (e:es))
>   = do es' <- remBuild (ReCat es)
>        e'  <- remBuild e
>        remBuildOne (SReCat e' es')
> remBuild (ReOpt e)
>   = do e2 <- remBuild e
>        e1 <- remLambda
>        remBuildOne (SReOr e1 e2)
> remBuild (ReStar e)
>   = do e' <- remBuild e
>        remBuildOne (SReStar e')
> remBuild (RePlus e)
>   = do e1 <- remBuild e
>        e2 <- remBuildOne (SReStar e1)
>        remBuildOne (SReCat e1 e2)
> remBuild (ReTerm [])
>   = remLambda
> remBuild (ReTerm [t])
>   = remBuildOne (SReTerm t)
> remBuild (ReTerm (t:ts))
>   = do ts' <- remBuild (ReTerm ts)
>        t'  <- remBuildOne (SReTerm t)
>        remBuildOne (SReCat t' ts')


Dfa construction

> data ReDfaState t
>   = ReDfaState {
>         dfaFinal :: Bool,
>       dfaTrans :: [(t, SimplRe t)]
>   }
>       deriving (Show)

> remMakeDfa :: (ReVars m t) => SimplRe t -> ReM m t ()
> remMakeDfa start
>   = do lams  <- remLambda
>        nulls <- remNullSet
>        remPush [lams, nulls, start]
>        remMakeDfa'
>   where
>     remMakeDfa'
>       = remPop >>= \ maybere ->
>           case maybere of
>               Just re -> processState re >> remStateDone re >> remMakeDfa'
>               Nothing -> return ()

>     processState re
>       = remLookupFwd re >>= \ info ->
>           case reiDfa info of
>               Just dfa -> return dfa
>               Nothing  -> expandState re info (reiSRE info)

>     expandState re info (SReCat e1 e2)
>       = do    dfa1 <- processState e1
>               trans1 <- makeCatTrans (dfaTrans dfa1) e2
>               trans <- if dfaFinal dfa1
>                        then processState e2 >>= \dfa2 ->
>                               makeOrTrans trans1 (dfaTrans dfa2)
>                        else return trans1
>               remPush (map snd trans)
>               remSetDfaState re
>                       (ReDfaState {
>                               dfaFinal = reiNullable info,
>                               dfaTrans = trans
>                       })
>     expandState re info (SReOr e1 e2)
>       = do    dfa1 <- processState e1
>               dfa2 <- processState e2
>               trans <- makeOrTrans (dfaTrans dfa1) (dfaTrans dfa2)
>               remPush (map snd trans)
>               remSetDfaState re
>                       (ReDfaState {
>                               dfaFinal = reiNullable info,
>                               dfaTrans = trans
>                       })
>     expandState re info (SReStar e)
>       = do    dfa <- processState e
>               let trans' = dfaTrans dfa
>               trans <- makeCatTrans trans' re
>               remPush (map snd trans)
>               remSetDfaState re
>                       (ReDfaState {
>                               dfaFinal = True,
>                               dfaTrans = trans
>                       })
>     expandState re info (SReTerm t)
>       = do    e2' <- remLambda
>               remPush [e2']
>               remSetDfaState re
>                       (ReDfaState {
>                               dfaFinal = False,
>                               dfaTrans = [(t,e2')]
>                       })
>     expandState re info SReLambda
>       = remSetDfaState re (ReDfaState { dfaFinal = True, dfaTrans = [] })
>     expandState re info SReNullSet
>       = remSetDfaState re (ReDfaState { dfaFinal = False, dfaTrans = [] })

> makeOrTrans :: (ReVars m t) => [(t, SimplRe t)]
>                       -> [(t, SimplRe t)] -> ReM m t [(t, SimplRe t)]
> makeOrTrans [] ts2
>     = return ts2
> makeOrTrans ts1 []
>     = return ts1
> makeOrTrans ts1'@(tr1@(t1,s1):ts1) ts2'@(tr2@(t2,s2):ts2)
>     | t1 < t2   = makeOrTrans ts1 ts2' >>= \ts -> return (tr1:ts)
>     | t1 > t2   = makeOrTrans ts1' ts2 >>= \ts -> return (tr2:ts)
>     | otherwise = remBuildOne (SReOr s1 s2) >>= \t ->
>                       makeOrTrans ts1 ts2 >>= \ts ->
>                           return ((t1,t):ts)

> makeCatTrans :: (ReVars m t) => [(t, SimplRe t)]
>                       -> SimplRe t -> ReM m t [(t, SimplRe t)]
> makeCatTrans [] _
>     = return []
> makeCatTrans ((t,s):ts) next
>     = do
>        s'  <- remBuildOne (SReCat s next)
>        ts' <- makeCatTrans ts next
>        return ((t,s'):ts')


Recursive Dfa

> data RDfa t
>   = RDfa Bool [(t, RDfa t)]

> matchRecursiveDfa :: (Ord t) => RDfa t -> [t] -> Bool
> matchRecursiveDfa (RDfa final trans) []
>   = final
> matchRecursiveDfa (RDfa final trans) (x:xs)
>   = case [ s | (t, s) <- trans, t == x ] of
>       []    -> False
>       (s:_) -> matchRecursiveDfa s xs

> remMakeRecursiveDfa :: (ReVars m t) => SimplRe t -> ReM m t (RDfa t)
> remMakeRecursiveDfa start
>   = do max1 <- gets resNext
>        fwd <- gets resFwdMap
>        let max = max1 - 1
>            stateArray = A.array (0,max)
>               [ (i, makeState stateArray fwd i) | i <- [0..max] ]
>        return (stateArray A.! start)                              -- PROBLEM
>   where
>       makeState :: (Ord t) => A.Array (SimplRe t) (RDfa t) ->
>                       M.Map (SimplRe t) (ReInfo t) ->
>                       SimplRe t -> RDfa t
>       makeState stateArray fwd s
>         = RDfa (dfaFinal dfastate) [ (t, stateArray A.! ts)        -- PROBLEM
>               | (t, ts) <- dfaTrans dfastate ]
>         where
>               Just reinfo = M.lookup s fwd                          -- PROBLEM
>               Just dfastate = reiDfa reinfo


Code generation.  This is very, very ugly.

> data BinTree a = BTZ | BTB (BinTree a) a (BinTree a) deriving (Show)

> listToBinTree :: [a] -> BinTree a
> listToBinTree l
>  = listToBinTree' (length l) l
>  where
>       listToBinTree' _ [] = BTZ
>       listToBinTree' n ls
>         = BTB (listToBinTree' n2 (take n2 ls)) t (listToBinTree' (n-n2-1) ts)
>         where
>               n2 = n `div` 2
>               t:ts = drop n2 ls

> remCodeGen :: (ReVars m t) => SimplRe t -> ReM m t ([t] -> Bool)
> remCodeGen start
>  = do max1 <- gets resNext
>       fwd <- gets resFwdMap
>       let max = max1 - 1
>           stateArray = A.array (0,max)
>               [ (i, makeState stateArray fwd i) | i <- [0..max] ]
>       return $ (stateArray A.! start)                              -- PROBLEM
>  where
>       globalFail = False
>       globalSucc = True
>
>       makeState :: (Ord t) => A.Array (SimplRe t) ([t] -> Bool) ->
>                       M.Map (SimplRe t) (ReInfo t) ->
>                       SimplRe t -> ([t] -> Bool)
>       makeState stateArray fwd s
>         | dfaFinal dfastate
>               = \ts -> -- trace ("In state " ++ show s) $
>                       case ts of
>                           []     -> globalSucc
>                           (t:ts) -> transition t ts
>         | otherwise
>               = \ts -> -- trace ("In state " ++ show s) $
>                       case ts of
>                           []     -> globalFail
>                           (t:ts) -> transition t ts
>         where
>               Just reinfo = M.lookup s fwd                         -- PROBLEM
>               Just dfastate = reiDfa reinfo
>
>               transition t ts
>                 = transition' (listToBinTree (dfaTrans dfastate)) t ts
>                 where
>                       transition' BTZ = \t ts -> globalFail
>                       transition' (BTB BTZ (x,st) BTZ)
>                         = \t ts ->
>                               if x == t then (stateArray A.! st) ts  -- PROBLEM
>                               else globalFail
>                       transition' (BTB l (x,st) r)
>                         = \t ts ->
>                               if t < x then transition' l t ts
>                               else if t > x then transition' r t ts
>                               else (stateArray A.! st) ts

Debug code.  Note that we need some extra constraints so we can
actually show regular expression states.

> class (ReVars m t, MonadIO m, Show t) => ReVarsIO m t where { }
> instance (ReVars m t, MonadIO m, Show t) => ReVarsIO m t where { }

> remDump :: (ReVarsIO m t) => ReM m t ()
> remDump
>   = do states <- gets (M.toList . resFwdMap)
>        remDumpStates states
>   where
>       remDumpStates [] = return ()
>       remDumpStates ((s,sr):ss)
>         = do  info <- remLookupFwd s
>               liftIO . putStrLn $ show s ++ ": " ++ show sr
>               remDumpStates ss

> remDumpDfa :: (ReVarsIO m t) => SimplRe t -> ReM m t ()
> remDumpDfa start
>   = do states <- gets (nodups . L.sort . resStatesDone)
>        liftIO (putStrLn $ "Initial state: " ++ show start)
>        remDumpStates states
>   where
>       nodups [] = []
>       nodups (x:xs)
>         = x : nodups (dropWhile (==x) xs)
>       remDumpStates [] = return ()
>       remDumpStates (s:ss)
>         = do  info <- remLookupFwd s
>               let Just dfaState = reiDfa info
>               liftIO . putStrLn $ show s ++ ": " ++ show dfaState
>               remDumpStates ss

> remTestBuild :: (ReVarsIO m t) => Re t -> m ()
> remTestBuild re
>  = remRun testBuild
>  where
>    testBuild
>       = do    s <- remBuild re
>               liftIO . putStrLn $ "Initial node: " ++ show s
>               remDump

> remTestDfa :: (ReVarsIO m t) => Re t -> m ()
> remTestDfa re
>  = remRun testDfa
>  where
>    testDfa
>       = do    s <- remBuild re
>               remMakeDfa s
>               remDumpDfa s

Wrapper

> makeDfa :: (Ord t) => Re t -> RDfa t
> makeDfa re
>   = runIdentity . remRun $ builder
>   where
>       builder
>         = do  s <- remBuild re
>               remMakeDfa s
>               remMakeRecursiveDfa s

> makeCode :: (Ord t) => Re t -> [t] -> Bool
> makeCode re
>   = runIdentity . remRun $ builder
>   where
>       builder
>         = do  s <- remBuild re
>               remMakeDfa s
>               remCodeGen s

> matchRe :: (Ord t) => Re t -> [t] -> Bool
> matchRe re
>   = makeCode re

> matchRe2 :: (Ord t) => Re t -> [t] -> Bool
> matchRe2 re
>   = matchRecursiveDfa (makeDfa re)

Test cases

> re1 :: Re Char
> re1 = ReOr [ReStar (ReCat [re0, re01]), ReStar (ReCat [re01, re0])]
>     where
>       re01 = ReOr [re0, re1]
>       re0 = ReTerm "0"
>       re1 = ReTerm "1"

[+\-]?{digit}*(\.{digit}+)?([eE][+\-]?{digit}+)?

> re2 :: Re Char
> re2 = ReCat [ReOpt (alt "+-"),
>       ReOr [ReCat [digits1, ReOpt (ReCat [dot, digits0])],
>             ReCat [digits0, dot, digits1]],
>       ReOpt (ReCat [alt "eE", ReOpt (alt "+-"), digits1])]
>     where
>       alt cs = ReOr $ map (\c -> ReTerm [c]) cs
>       digits0 = ReStar digit
>       digits1 = RePlus digit
>       digit = alt "0123456789"
>       dot = ReTerm "."

