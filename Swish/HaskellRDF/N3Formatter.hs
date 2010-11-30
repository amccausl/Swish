--------------------------------------------------------------------------------
--  $Id: N3Formatter.hs,v 1.23 2004/01/22 19:52:41 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  N3Formatter
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This Module implements a Notation 3 formatter (see [1], [2]),
--  for an RDFGraph value.
--
--
-- REFERENCES:
--
-- [1] http://www.w3.org/DesignIssues/Notation3.html
--     Tim Berners-Lee's design issues series notes and description
--
-- [2] http://www.w3.org/2000/10/swap/Primer.html
--     Notation 3 Primer by Sean Palmer
--
--
--  [[[TODO:]]]
--  (a) Initial prefix list to include nested formulae;
--      then don't need to update prefix list for these.
--  (b) blank nodes used just once, can be expanded inline using
--      [...] syntax.
--  (c) generate multi-line literals when appropriate
--  (d) more flexible terminator generation for formatted formulae
--      (for inline blank nodes.)
--
--------------------------------------------------------------------------------

module Swish.HaskellRDF.N3Formatter
    ( formatGraphAsStringNl
    , formatGraphAsString
    , formatGraphAsShowS
    , formatGraphIndent
    , formatGraphDiag
    )
where

import Swish.HaskellRDF.RDFGraph
    ( RDFGraph, RDFLabel(..)
    , NamespaceMap, RevNamespaceMap
    , emptyNamespaceMap
    , FormulaMap, emptyFormulaMap
    , getArcs, labels
    , setNamespaces, getNamespaces
    , getFormulae
    , emptyRDFGraph
    )

import Swish.HaskellRDF.GraphClass
    ( Arc(..)
    , arc
    )

import Swish.HaskellUtils.LookupMap
    ( LookupEntryClass(..)
    , LookupMap, emptyLookupMap, reverseLookupMap
    , listLookupMap
    , mapFind, mapFindMaybe, mapAdd, mapDelete, mapMerge
    )

import Swish.HaskellUtils.QName
    ( QName(..)
    , newQName, qnameFromPair, qnameFromURI
    , getNamespace, getLocalName, getQNameURI
    , splitURI
    )

import Swish.HaskellUtils.Namespace
    ( ScopedName(..), getScopeURI )

import Swish.HaskellUtils.ProcessURI
    ( isAbsoluteURIRef )

import Swish.HaskellRDF.Sort.QuickSort
    ( stableQuickSort )

import Data.Char
    ( isDigit )

import Data.List
    ( groupBy )

import Data.Maybe
    ( Maybe(..), isJust, fromJust )

----------------------------------------------------------------------
--  Ouptut string concatenation
----------------------------------------------------------------------
--
--  Function puts uses the shows mechanism to avoid the cost of
--  quadratic string concatenation times.  (Use function composition to
--  concatenate strings thus reprersented.)

puts :: String -> ShowS
puts = showString

----------------------------------------------------------------------
--  Graph formatting state monad
----------------------------------------------------------------------
--
--  The graph to be formatted is carried as part of the formatting
--  state, so that decisions about what needs to be formatted can
--  themselves be based upon and reflected in the state (e.g. if a
--  decision is made to include a blank node inline, it can be removed
--  from the graph state that remains to be formatted).

type SubjTree lb = [(lb,PredTree lb)]
type PredTree lb = [(lb,[lb])]

data Fgs = Fgs
    { indent    :: String
    , lineBreak :: Bool
    , graph     :: RDFGraph
    , subjs     :: SubjTree RDFLabel
    , props     :: PredTree RDFLabel   -- for last subject selected
    , objs      :: [RDFLabel]          -- for last property selected
    , formAvail :: FormulaMap RDFLabel
    , formQueue :: [(RDFLabel,RDFGraph)]
    , nodeGenSt :: NodeGenState
    , traceBuf  :: [String]
    }

emptyFgs :: NodeGenState -> Fgs
emptyFgs ngs = Fgs
    { indent    = "\n"
    , lineBreak = False
    , graph     = emptyRDFGraph
    , subjs     = []
    , props     = []
    , objs      = []
    , formAvail = emptyFormulaMap
    , formQueue = []
    , nodeGenSt = ngs
    , traceBuf  = []
    }

--  Node name generation state information that carries through
--  and is updated by nested formulae

type NodeGenLookupMap = LookupMap (RDFLabel,Int)

data NodeGenState = Ngs
    { prefixes  :: NamespaceMap
    , nodeMap   :: NodeGenLookupMap
    , nodeGen   :: Int
    }

emptyNgs :: NodeGenState
emptyNgs = Ngs
    { prefixes  = emptyLookupMap
    , nodeMap   = emptyLookupMap
    , nodeGen   = 0
    }

--  monad definition adapted from Simon Thompson's book, p410
--
--  Fgsm a is a "state transformer" on a state of type "Fgs",
--  which additionally returns a value of type 'a'.
data Fgsm a = Fgsm ( Fgs -> (Fgs,a) )

instance Monad Fgsm where
    return res      = Fgsm (\fgs -> (fgs,res))
    (Fgsm st) >>= f = Fgsm (\fgs ->
        let (newfgs,res) = st fgs
            (Fgsm st')   = f res
        in
            st' newfgs
        )

getFgs :: Fgsm Fgs
getFgs = Fgsm (\fgs -> (fgs,fgs) )

doTrace :: String -> Fgsm ()
doTrace msg = Fgsm (\fgs -> (fgs {traceBuf=msg:(traceBuf fgs)},()) )

getIndent :: Fgsm String
getIndent = Fgsm (\fgs -> (fgs,indent fgs) )

setIndent :: String -> Fgsm ()
setIndent ind = Fgsm (\fgs -> (fgs {indent=ind},()) )

getLineBreak :: Fgsm Bool
getLineBreak = Fgsm (\fgs -> (fgs,lineBreak fgs) )

setLineBreak :: Bool -> Fgsm ()
setLineBreak brk = Fgsm (\fgs -> (fgs {lineBreak=brk},()) )

getNgs :: Fgsm NodeGenState
getNgs = Fgsm (\fgs -> (fgs,nodeGenSt fgs) )

setNgs :: NodeGenState -> Fgsm ()
setNgs ngs = Fgsm (\fgs -> (fgs { nodeGenSt = ngs },()) )

getPrefixes :: Fgsm NamespaceMap
getPrefixes = Fgsm (\fgs -> (fgs,prefixes (nodeGenSt fgs)) )

queueFormula :: RDFLabel -> Fgsm ()
queueFormula fn = Fgsm (\fgs ->
    let fa = formAvail fgs
        newState fv =
            fgs { formAvail=mapDelete fa fn
                , formQueue=(fn,fv):(formQueue fgs)
                }
    in
        case (mapFindMaybe fn fa) of
            Nothing -> (fgs,())
            Just fv -> (newState fv,())
    )

moreFormulae :: Fgsm Bool
moreFormulae =  Fgsm (\fgs -> (fgs,not $ null (formQueue fgs)) )

nextFormula :: Fgsm (RDFLabel,RDFGraph)
nextFormula =  Fgsm (\fgs ->
    let (nf:fq) = (formQueue fgs) in (fgs {formQueue=fq},nf)
    )

----------------------------------------------------------------------
--  Define a top-level formatter function:
--  accepts a graph and returns a string
----------------------------------------------------------------------

formatGraphAsStringNl :: RDFGraph -> String
formatGraphAsStringNl gr = formatGraphAsShowS gr "\n"

formatGraphAsString :: RDFGraph -> String
formatGraphAsString gr = formatGraphAsShowS gr ""

formatGraphAsShowS :: RDFGraph -> ShowS
formatGraphAsShowS gr = formatGraphIndent "\n" True gr
{- old code:
    where
        (out,_,_,_) = formatGraphDiag gr
-}

formatGraphIndent :: String -> Bool -> RDFGraph -> ShowS
formatGraphIndent ind dopref gr = out
    where
        (_,out) = formatGraphDiag1 ind dopref emptyLookupMap gr

--  Format graph and return additional information
formatGraphDiag ::
    RDFGraph -> (ShowS,NodeGenLookupMap,Int,[String])
formatGraphDiag gr = (out,nodeMap ngs,nodeGen ngs,traceBuf fgs)
    where
        (fgs,out) = formatGraphDiag1 "\n" True emptyLookupMap gr
        ngs       = nodeGenSt fgs

--  Internal function starts with supplied prefix table and indent string,
--  and returns final state and formatted string.
--  This is provided for diagnostic access to the final state
formatGraphDiag1 :: String -> Bool -> NamespaceMap -> RDFGraph -> (Fgs,ShowS)
formatGraphDiag1 ind dopref pref gr = res where
    Fgsm fg = formatGraph ind " ." False dopref gr  -- construct monad
    ngs     = emptyNgs                  -- construct initial state
                { prefixes=pref
                , nodeGen=findMaxBnode gr
                }
    (_,res) = fg (emptyFgs ngs)         -- apply monad to state, pick result

----------------------------------------------------------------------
--  Formatting as a monad-based computation
----------------------------------------------------------------------

-- ind      is indentation string
-- end      is ending string to be placed after final statement
-- dobreak  is True if a line break is to be inserted at the start
-- dopref   is True if prefix strings are to be generated
--
formatGraph :: String -> String -> Bool -> Bool -> RDFGraph -> Fgsm (Fgs,ShowS)
formatGraph ind end dobreak dopref gr =
    do  { setIndent ind
        ; setLineBreak dobreak
        ; setGraph gr
        ; fp <- if dopref then
                    formatPrefixes (getNamespaces gr)
                else
                    return $ puts ""
        ; more <- moreSubjects
        ; res  <- if more then do
            { fr <- formatSubjects
            ; return $ fp . fr . (puts end)
            }
          else return $ fp
        ; fgs <- getFgs
        ; return (fgs,res)
        }

formatPrefixes :: NamespaceMap -> Fgsm ShowS
formatPrefixes pmap =
    do  { let mls = map (pref . keyVal) (listLookupMap pmap)
        ; ls <- sequence mls
        ; return $ puts $ concat ls
        }
    where
        pref (p,u) = nextLine $ "@prefix "++p++": <"++u++"> ."

--  The above function creates a list of 'Fgsm String' monads, then
--  uses 'sequence' to turn that to a single 'Fgsm [String]' and finally
--  concatenates them to a single string and uses 'puts' to return the
--  result as a 'Fgsm ShowS'.  Phew!

formatSubjects :: Fgsm ShowS
formatSubjects =
    do  { sb    <- nextSubject
        ; sbstr <- formatLabel sb
        ; prstr <- formatProperties sb sbstr
        ; fmstr <- formatFormulae ""
        ; more  <- moreSubjects
        ; if more then do
            { fr <- formatSubjects
            ; return $ (puts $ prstr ++ fmstr ++ " .") . fr
            }
          else return $ puts $ prstr ++ fmstr
        }

formatProperties :: RDFLabel -> String -> Fgsm String
formatProperties sb sbstr =
    do  { pr    <- nextProperty sb
        ; prstr <- formatLabel pr
        ; obstr <- formatObjects sb pr (sbstr++" "++prstr)
        ; more  <- moreProperties
        ; let sbindent = replicate (length sbstr) ' '
        ; if more then do
            { fr <- formatProperties sb sbindent
            ; nl <- nextLine $ obstr ++ " ;"
            ; return $ nl ++ fr
            }
          else nextLine $ obstr
        }

formatObjects :: RDFLabel -> RDFLabel -> String -> Fgsm String
formatObjects sb pr prstr =
    do  { ob    <- nextObject sb pr
        ; obstr <- formatLabel ob
        ; more  <- moreObjects
        ; if more then do
            { let prindent = replicate (length prstr) ' '
            ; fr <- formatObjects sb pr prindent
            ; nl <- nextLine $ prstr ++ " " ++ obstr ++ ","
            ; return $ nl ++ fr
            }
          else return $ prstr ++ " " ++ obstr
        }

formatFormulae :: String -> Fgsm String
formatFormulae fp =
    do  { more  <- moreFormulae
        ; if more then do
            { fnlgr <- nextFormula
            ; fnstr <- formatFormula fnlgr
            ; formatFormulae $ fp ++ " ." ++ fnstr
            }
          else return $ fp
        }

-- [[[TODO: use above pattern for subject/property/object loops?]]]

formatFormula :: (RDFLabel,RDFGraph) -> Fgsm String
formatFormula (fn,gr) =
    do  { fnstr <- formatLabel fn
        ; f1str <- nextLine $ fnstr ++ " :-"
        ; f2str <- nextLine "    {"
        ; ngs0  <- getNgs
        ; ind   <- getIndent
        ; let Fgsm grm = formatGraph (ind++"    ") "" True False
                                     (setNamespaces emptyNamespaceMap gr)
        ; let (fgs',(_,f3str)) = grm (emptyFgs ngs0)
        ; setNgs (nodeGenSt fgs')
        ; f4str <- nextLine "    }"
        ; return $ f1str ++ f2str ++ (f3str f4str)
        }

----------------------------------------------------------------------
--  Formatting helpers
----------------------------------------------------------------------

setGraph        :: RDFGraph -> Fgsm ()
setGraph gr =
    Fgsm (\fgs ->
        let ngs0 = (nodeGenSt fgs)
            pre' = mapMerge (prefixes ngs0) (getNamespaces gr)
            ngs' = ngs0 { prefixes=pre' }
            fgs' = fgs  { graph     = gr
                        , subjs     = arcTree $ getArcs gr
                        , props     = []
                        , objs      = []
                        , formAvail = getFormulae gr
                        , nodeGenSt = ngs'
                        }
        in (fgs',()) )

moreSubjects    :: Fgsm Bool
moreSubjects    = Fgsm (\fgs -> (fgs,not $ null (subjs fgs)))

nextSubject     :: Fgsm RDFLabel
nextSubject     =
    Fgsm (\fgs ->
        let sb:sbs = subjs fgs
            fgs' = fgs  { subjs = sbs
                        , props = snd sb
                        , objs  = []
                        }
        in (fgs',fst sb) )


moreProperties  :: Fgsm Bool
moreProperties  = Fgsm (\fgs -> (fgs,not $ null (props fgs)))

nextProperty    :: RDFLabel -> Fgsm RDFLabel
nextProperty sb =
    Fgsm (\fgs ->
        let pr:prs = props fgs
            fgs' = fgs  { props = prs
                        , objs  = snd pr
                        }
        in (fgs',fst pr) )


moreObjects     :: Fgsm Bool
moreObjects     = Fgsm (\fgs -> (fgs,not $ null (objs fgs)))

nextObject      :: RDFLabel -> RDFLabel -> Fgsm RDFLabel
nextObject sb pr =
    Fgsm (\fgs ->
        let ob:obs = objs fgs
            fgs'   = fgs { objs = obs }
        in (fgs',ob) )

nextLine        :: String -> Fgsm String
nextLine str =
    do  { ind <- getIndent
        ; brk <- getLineBreak
        ; if brk then
            return $ ind++str
          else
            --  After first line, always insert line break
            do  { setLineBreak True
                ; return str
                }
        }

--  Format a label
--  Most labels are simply displayed as provided, but there are a
--  number of wrinkles to take care of here:
--  (a) blank nodes automatically allocated on input, with node
--      identifiers of the form of a digit string nnn.  These are
--      not syntactically valid, and are reassigned node identifiers
--      of the form _nnn, where nnn is chosen so that is does not
--      clash with any other identifier in the graph.
--  (b) URI nodes:  if possible, replace URI with qname,
--      else display as <uri>
--  (c) formula nodes (containing graphs).
--
--  [[[TODO:]]]
--  (d) blank nodes used just once, can be expanded inline using
--      [...] syntax.
--  (e) generate multi-line literals when appropriate

formatLabel :: RDFLabel -> Fgsm String
formatLabel lab@(Blank nodeid@(lnc:_)) =
    do  { name <- formatNodeId lab
        ; queueFormula lab
        ; return name
        }
formatLabel lab@(Res sn) =
    do  { pr <- getPrefixes
        ; let nsuri  = getScopeURI sn
        ; let local  = snLocal sn
        ; let premap = reverseLookupMap pr :: RevNamespaceMap
        ; let prefix = mapFindMaybe nsuri premap
        ; let name   = if (isJust prefix)
                        then fromJust prefix++":"++local
                        else "<"++nsuri++local++">"
        ; queueFormula lab
        ; return name
        }
{-
formatLabel lab@(Lit str typ) =
    do  { return $ show lab
        }
formatLabel lab@(Var vid) =
    do  { return $ show lab
        }
-}
formatLabel lab =
    do  { return $ show lab
        }

formatNodeId :: RDFLabel -> Fgsm String
formatNodeId lab@(Blank nodeid@(lnc:_)) =
    if isDigit lnc then mapBlankNode lab else return $ show lab

mapBlankNode :: RDFLabel -> Fgsm String
mapBlankNode lab =
    do  { ngs <- getNgs
        ; let nmap = nodeMap ngs
        ; let nnxt = (nodeGen ngs)
        ; (nval,nnxt',nmap') <- case mapFind 0 lab nmap of
            0 -> do { let nn = nnxt + 1
                    ; let nm = mapAdd nmap (lab,nn)
                    ; setNgs $ ngs { nodeGen=nn, nodeMap=nm }
                    ; return (nn,nn,nm)
                    }
            n -> return $ (n,nnxt,nmap)
        {- ; doTrace $ "Map node id: "++(show lab)
                        ++", nval "++(show nval)
                        ++", next "++(show nnxt')
                        ++", nmap "++(show nmap') -}
        ; return $ show $ Blank ('_':show nval)
        }

----------------------------------------------------------------------
--  Graph-related helper functions
----------------------------------------------------------------------

--  Rearrange a list of arcs into a tree of pairs which group together
--  all statements for a single subject, sind similarly for multiple
--  objects of a common predicate.
arcTree :: (Ord lb) => [Arc lb] -> SubjTree lb
arcTree as = commonFstEq (commonFstEq id) $ map spopair $ stableQuickSort as
    where
        spopair (Arc s p o) = (s,(p,o))

{-
arcTree as = map spopair $ sort as
    where
        spopair (Arc s p o) = (s,[(p,[o])])
-}

--  Rearrange a list of pairs so that multiple occurrences of the first
--  are commoned up, and the supplied function is applied to each sublist
--  with common first elements to obtain the corresponding second value
commonFstEq :: (Eq a) => ( [b] -> c ) -> [(a,b)] -> [(a,c)]
commonFstEq f ps =
    [ (fst $ head sps,f $ map snd sps) | sps <- groupBy fstEq ps ]
    where
        fstEq (f1,_) (f2,_) = f1 == f2

{-
-- Diagnostic code for checking arcTree logic:
testArcTree = (arcTree testArcTree1) == testArcTree2
testArcTree1 =
    [Arc "s1" "p11" "o111", Arc "s1" "p11" "o112"
    ,Arc "s1" "p12" "o121", Arc "s1" "p12" "o122"
    ,Arc "s2" "p21" "o211", Arc "s2" "p21" "o212"
    ,Arc "s2" "p22" "o221", Arc "s2" "p22" "o222"
    ]
testArcTree2 =
    [("s1",[("p11",["o111","o112"]),("p12",["o121","o122"])])
    ,("s2",[("p21",["o211","o212"]),("p22",["o221","o222"])])
    ]
-}


findMaxBnode    :: RDFGraph -> Int
findMaxBnode gr =
    maximum $
    map getAutoBnodeIndex $
    labels gr

getAutoBnodeIndex   :: RDFLabel -> Int
getAutoBnodeIndex (Blank ('_':lns)) = res where
    -- cf. prelude definition of read s ...
    res = case [x | (x,t) <- reads lns, ("","") <- lex t] of
            [x] -> x
            _   -> 0
getAutoBnodeIndex _                   = 0



--------------------------------------------------------------------------------
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--
--  This file is part of Swish.
--
--  Swish is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or
--  (at your option) any later version.
--
--  Swish is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with Swish; if not, write to:
--    The Free Software Foundation, Inc.,
--    59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
--
--------------------------------------------------------------------------------
-- $Source: /file/cvsdev/HaskellRDF/N3Formatter.hs,v $
-- $Author: graham $
-- $Revision: 1.23 $
-- $Log: N3Formatter.hs,v $
-- Revision 1.23  2004/01/22 19:52:41  graham
-- Rename module URI to avoid awkward clash with Haskell libraries
--
-- Revision 1.22  2004/01/09 12:57:08  graham
-- Remove space between perfix and ':' in @prefix declaractions,
-- for compatibility with new Notation 3 syntax (and Jena).
--
-- Revision 1.21  2004/01/09 12:49:39  graham
-- Remove superfluous PutS class.
--
-- Revision 1.20  2004/01/09 12:44:52  graham
-- Fix up N3Formatter to suppress final statement-terminating '.' in a formula,
-- for compatibility with the current Notation3 syntax.
--
-- Revision 1.19  2004/01/07 19:49:12  graham
-- Reorganized RDFLabel details to eliminate separate language field,
-- and to use ScopedName rather than QName.
-- Removed some duplicated functions from module Namespace.
--
-- Revision 1.18  2003/12/05 02:31:32  graham
-- Script parsing complete.
-- Some Swish script functions run successfully.
-- Command execution to be completed.
--
-- Revision 1.17  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.16  2003/11/24 15:46:04  graham
-- Rationalize N3Parser and N3Formatter to use revised vocabulary
-- terms defined in Namespace.hs
--
-- Revision 1.15  2003/10/24 21:03:25  graham
-- Changed kind-structure of LookupMap type classes.
--
-- Revision 1.14  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.13  2003/09/24 13:36:42  graham
-- QName handling separated from RDFGraph module, and
-- QName splitting moved from URI module to QName module.
--
-- Revision 1.12  2003/06/25 21:16:52  graham
-- Reworked N3 formatting logic to support proof display.
-- Basic proof display is working.
--
-- Revision 1.11  2003/06/12 00:47:55  graham
-- Allowed variable node (?v) and bare anonymous nodes in N3 parser.
--
-- Revision 1.10  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.9  2003/05/28 17:39:30  graham
-- Trying to track down N3 formatter performance problem.
--
-- Revision 1.8  2003/05/23 00:02:42  graham
-- Fixed blank node id generation bug in N3Formatter
--
-- Revision 1.7  2003/05/20 23:35:28  graham
-- Modified code to compile with GHC hierarchical libraries
--
-- Revision 1.6  2003/05/14 22:39:23  graham
-- Initial formatter tests all run OK.
-- The formatter could still use so,me improvement,
-- but it
-- passes the minimal round-tripping tests.
--
-- Revision 1.5  2003/05/14 19:38:32  graham
-- Simple formatter tests all working with reworked graph and lookup structures.
-- More complex formatter tests still to be coded.
--
-- Revision 1.4  2003/04/29 22:09:43  graham
-- Updated TODO notes
--
-- Revision 1.3  2003/04/29 22:07:10  graham
-- Some refactoring of N3 formatter.
-- N3 formatter now handles trivial cases.
-- More complex formatter test cases still to be developed.
--
-- Revision 1.2  2003/04/25 11:40:06  graham
-- Formatter compiles OK
--
-- Revision 1.1  2003/04/24 23:41:39  graham
-- Added Ord class membership to graph nodes
-- Added empty lookup table definition
-- Started on N3 formatter module
--
