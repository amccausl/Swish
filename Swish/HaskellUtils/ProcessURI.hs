--------------------------------------------------------------------------------
--  $Id: ProcessURI.hs,v 1.1 2004/01/22 19:52:27 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ProcessURI
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a collection of functions for manipulating URIs.
--
--  Functions provided deal with:
--    Validating and parsing URI syntax
--    Separating a fragment from a URI
--    Separating URI into QName and local name
--    Relative URI computations
--
--  The primary reference for URI handling is RFC2396 [1],
--  as updated by RFC 2732 [2].
--  RFC 1808 [3] contains a number of test cases for relative URI handling.
--  Dan Connolly's Python module 'uripath.py' [4] also contains useful details
--  and test cases.
--
--  [1] http://www.ietf.org/rfc/rfc2396.txt
--  [2] http://www.ietf.org/rfc/rfc2732.txt
--  [3] http://www.ietf.org/rfc/rfc1808.txt
--  [4] http://www.w3.org/2000/10/swap/uripath.py
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.ProcessURI
    ( URI(URI)
    , isValidURIRef, isAbsoluteURIRef, isAbsoluteURI
    , parseURIRef, parseAbsoluteURIRef, parseAbsoluteURI
    , getURIRef, normalizeURI, compareURI, normSeg, normSeg1, mergeSeg
    , splitURIFragment, makeURIWithFragment -- , splitQName
    , relativeRefPart, absoluteUriPart
    )
where

import Swish.HaskellUtils.ParseURI
import Swish.HaskellUtils.Parse
-- type Parser a b = Parse.Parser a b
-- isValid         = Parse.isValid
-- parseApply      = Parse.parseApply


-- Test supplied string for valid URI syntax
isValidURIRef :: String -> Bool
isValidURIRef = isValid parseURIRef

-- Test supplied string for valid absolute URI reference syntax
isAbsoluteURIRef :: String -> Bool
isAbsoluteURIRef = isValid parseAbsoluteURIRef

-- Test supplied string for valid absolute URI syntax
isAbsoluteURI :: String -> Bool
isAbsoluteURI = isValid parseAbsoluteURI

-- URI parser (see Parse and ParseURI modules)
parseURIRef :: Parser Char String
parseURIRef = uriReference `parseApply` uriToString

-- Absolute URI reference parser (see Parse module)
parseAbsoluteURIRef :: Parser Char String
parseAbsoluteURIRef = absoluteUriReference `parseApply` uriToString

-- Absolute URI parser (see Parse module)
parseAbsoluteURI :: Parser Char String
parseAbsoluteURI = absoluteUri `parseApply` uriToString

-- Parse and return URI reference as URI value
getURIRef :: String -> URI
getURIRef s = extractURIRef (uriReference s)
    where
    extractURIRef [(u,"")] = u
    extractURIRef [(_,_)]  = ( URI "" "" ["<invalid URI>"] "" "" )
    extractURIRef _        = ( URI "" "" ["<ambiguous URI>"] "" "" )

-- Normalize URI string
normalizeURI :: String -> String
normalizeURI str = uriToString (URI sc au (normSeg se) qu fr)
    where
    URI sc au se qu fr = getURIRef str

-- Compare two URIs
-- Takes account of normalizations that can be applied to all URIs
-- (2003-02-20, currently subject to W3C TAG debate)
compareURI :: String -> String -> Bool
compareURI u1 u2 = ( u1 == u2 )

-- Separate URI-with-fragment into URI and fragment ID
splitURIFragment :: String -> ( String, Maybe String )
    -- splitURIFragment "http://example.org/aaa#bbb" =
    --     ("http://example.org/aaa",Just "bbb")
    -- splitURIFragment "http://example.org/aaa" =
    --     ("http://example.org/aaa",Nothing)
splitURIFragment inp =
    case (uriReference inp) of
        [(URI s a p q f,"")] -> (uriToString (URI s a p q ""),pickFrag f)
        _ -> error ("splitURIFragment, Invalid URI: "++inp)
    where
        pickFrag ('#':f) = Just f
        pickFrag _       = Nothing

-- Construct URI-with-fragment using URI and supplied fragment id
makeURIWithFragment :: String -> Maybe String -> String
    -- makeURIWithFragment "http://example.org/aaa" (Just "fff") =
    --     "http://example.org/aaa#fff"
    -- makeURIWithFragment "http://example.org/aaa#bbb" (Just "fff") =
    --     "http://example.org/aaa#fff"
    -- makeURIWithFragment "http://example.org/aaa" Nothing
    --     "http://example.org/aaa"
    -- makeURIWithFragment "http://example.org/aaa#bbb" Nothing
    --     "http://example.org/aaa"
makeURIWithFragment base frag =
    case frag of
        Just f  -> b ++ "#" ++ f
        Nothing -> b
        where
            (b,_) = splitURIFragment base

-- Separate URI into QName URI and local name
splitQName :: String -> ( String, String )
    -- splitQname "http://example.org/aaa#bbb" = ("http://example.org/aaa#","bbb")
    -- splitQname "http://example.org/aaa/bbb" = ("http://example.org/aaa/","bbb")
    -- splitQname "http://example.org/aaa/"    = ("http://example.org/aaa/","")
splitQName qn = splitAt (scanQName qn (-1) 0) qn

-- helper function for splitQName
-- Takes 3 arguments:
--   QName to scan
--   index of last name-start char, or (-1)
--   number of characters scanned so far
-- Returns index of start of name, or length of list
--
scanQName :: String -> Int -> Int -> Int
scanQName (nextch:more) (-1) nc
    | isNameStartChar nextch  = scanQName more nc   (nc+1)
    | otherwise               = scanQName more (-1) (nc+1)
scanQName (nextch:more) ns nc
    | not (isNameChar nextch) = scanQName more (-1) (nc+1)
    | otherwise               = scanQName more ns   (nc+1)
scanQName "" (-1) nc = nc
scanQName "" ns   _  = ns

-- Definitions here per XML namespaces, NCName production,
-- restricted to characters used in URIs.
-- cf. http://www.w3.org/TR/REC-xml-names/
isNameStartChar c = ( isAlpha c ) || ( c == '_' )
isNameChar      c = ( isAlpha c ) || ( isDigit c ) || ( any (==c) ".-_" )

-- Get reference relative to given base
relativeRefPart :: String -> String -> String
    -- relativeRefPart "base:" "base:relativeRef" = "relativeRef"
    -- relativeRefPart "base:" "another:URI"      = "another:URI"
relativeRefPart base full =
    uriToString ( relPartRef ( getURIRef base ) ( getURIRef full ) )
    where
    relPartRef u1@(URI sc1 au1 se1 _ _) u2@( URI sc2 au2 se2 qu2 fr2 )
        | sc1 /= sc2 = URI sc2 au2 (normSeg se2) qu2 fr2    -- different schemes
        | opaque au1 = URI "" au2 (normSeg se2) qu2 fr2     -- same scheme, base is opaque
        | au1 /= au2 = URI "" au2 (normSeg se2) qu2 fr2     -- same scheme, different authority
        | otherwise  = URI "" "" (relPath (normSeg se1) (normSeg se2) ) qu2 fr2
    -- If paths share a leading segment (other than "/") then compute a path relative
    -- to the base URI, otherwise return a root-relative path
    relPath s1 []    = ["/"]
    relPath [] s2    = s2
    relPath ("/":s1h:s1t) s2@("/":s2h:s2t)
        | s1h == s2h = relPartSeg s1t s2t
        | otherwise  = s2
    relPath (s1h:s1t) s2@(s2h:s2t)
        | s1h == s2h = relPartSeg s1t s2t
        | otherwise  = s2
    {- relPath s1@(_:_) s2@(_:_) = relPartSeg s1 s2 [[[REDUNDANT?]]] -}
    -- Path-segment relative to base:
    -- (An alternative would be descendent relative to base, otherwise relative to root)
    --   relPartSeg a/b a/c -> c        (case 1:  common leading segments)
    --   relPartSeg a/b a/  -> ./       (case 1a: identical paths with empty name)
    --   relPartSeg a   b/c -> b/c      (case 2:  all base path segments used)
    --   relPartSeg b   c   -> c        (case 2)
    --   relPartSeg a   c/  -> c/       (case 2)
    --   relPartSeg ""  c   -> c        (case 2)
    --   relPartSeg a ""    -> ""       (case 2)
    --   relPartSeg a   c:d -> ./c:d    (case 2a: bare name looks like URI
    --   relPartSeg a/b c   -> ../c     (case 3: unused base path segments)
    --   relPartSeg a/b ""  -> ../      (case 3)
    --   relPartSeg a/  c   -> ../c     (case 3)
    --   relPartSeg a/  ""  -> ../      (case 3)
    -- NOTE the last element of the path segment lists are always the "name" component,
    -- and is present as an empty string if the path ends with a '/' character
    relPartSeg [_] [""]    = ["./",""]                  -- Case 1a
    relPartSeg [_] [st]
        | looksLikeURI st  = ["./",st]                  -- Case 2a
        | otherwise        = [st]                       -- Case 2
    relPartSeg [_] s2      = s2                         -- Case 2
    relPartSeg s1  [s2t]   = difPartSeg s1 [s2t]        -- Case 3  (this test should be redundant)
    relPartSeg s1@(s1h:s1t) s2@(s2h:s2t)
        | s1h == s2h = relPartSeg s1t s2t               -- Case 1
        | otherwise  = difPartSeg s1 s2                 -- Case 2 or 3 ...
    difPartSeg [_]     s2  = s2                         -- Case 2  (final base segment is ignored)
    difPartSeg (_:s1t) s2  = "../":(difPartSeg s1t s2)  -- Case 3

-- Get absolute URI given base and relative reference
-- NOTE:  absoluteURI base (relativeRef base u) is always equivalent to u.
-- cf. http://lists.w3.org/Archives/Public/uri/2003Jan/0008.html
absoluteUriPart :: String -> String -> String
    -- absoluteUriPart "base:" "relativeRef" = "base:relativeRef"
    -- absoluteUriPart "base:" "another:URI" = "another:URI"
absoluteUriPart base rel =
    uriToString ( joinRef ( getURIRef base ) ( getURIRef rel ) )
    where
    joinRef u1@(URI sc1 au1 se1 _ _) u2@( URI sc2 au2 se2 qu2 fr2 )
        -- non-validating case here?  (See RFC2396bis section 5.2)
        | sc2 /= ""     = u2
        | opaque au1    = URI sc1 au2 se2 qu2 fr2                       -- Base not relative
        | au2 /= ""     = URI sc1 au2 se2 qu2 fr2
        | se2 == []     = if qu2 == "" then URI "" "" [] "" fr2         -- Same document
                                       else URI sc1 au1 se1 qu2 fr2     -- Base document
        | otherwise     = URI sc1 au1 ( mergeSeg se1 se2 ) qu2 fr2

-- Test authority string for opaque form (non-null and not starting with '/')
opaque :: String -> Bool
opaque ""      = False
opaque ('/':_) = False
opaque _       = True

-- Merge segment se2 with base segment se1
mergeSeg :: [String] -> [String] -> [String]
mergeSeg _ s2@("/":se2) = normSeg s2
mergeSeg [] se2         = normSeg ("/":se2)
mergeSeg se1 se2        = normSeg ( (init se1) ++ se2 )

-- Normalize ./ and ../ in segment list:
-- Don't touch leading "/"
-- Don't allow "../" to cancel another "../"
-- Leave bare "./"
-- Remove any trailing "./"
normSeg :: [String] -> [String]
normSeg ("/":st)      = "/":(normSeg1 st)
normSeg st            = normSeg1 st

normSeg1 []           = []
normSeg1 ["./"]       = ["./"]
normSeg1 ["."]        = ["./",""]                      -- trailing '.' is treated as './'
normSeg1 [".."]       = ["../",""]                     -- trailing '..' is treated as '../'
normSeg1 p@["./",st]
    | looksLikeURI st = p
    | otherwise       = [st]
normSeg1 ("./":st)    = normSeg1 st
normSeg1 (s1:st)      = normSeg2 (s1:(normSeg1 st))    -- TEST CASE:  a/b/../../c

normSeg2 :: [String] -> [String]
normSeg2 s@("../":"../":st) = s
normSeg2 ["./","../"] = ["./"]
normSeg2 (_:"../":st) = st
normSeg2 [sh,"./"]    = [sh]
normSeg2 (sh:"./":st) = sh:st
normSeg2 ("./":st)    = st
normSeg2 st           = st

-- Test if string looks like a URI, by virtue of starting with a 'name:'
looksLikeURI :: String -> Bool
looksLikeURI name = not ( null ( relSegmentWithColon name ) )

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
--  Foobar is distributed in the hope that it will be useful,
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
-- $Source: /file/cvsdev/HaskellUtils/ProcessURI.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: ProcessURI.hs,v $
-- Revision 1.1  2004/01/22 19:52:27  graham
-- Rename module URI to avoid awkward clash with Haskell libraries
--
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.12  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.11  2003/09/24 13:35:44  graham
-- QName splitting moved from URI module to QName module
--
-- Revision 1.10  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.9  2003/05/28 19:57:50  graham
-- Adjusting code to compile with GHC
--
-- Revision 1.8  2003/03/05 22:16:23  graham
-- URI code passes all unit tests
--
-- Revision 1.7  2003/03/05 14:47:45  graham
-- Relative URI code complete, not tested
-- Fixed a URI parser bug
--
-- Revision 1.6  2003/02/28 14:02:52  graham
-- A few new test cases
--
-- Revision 1.5  2003/02/27 23:33:54  graham
-- QName splitting tested OK
--
-- Revision 1.4  2003/02/27 18:48:05  graham
-- Fix URI parser bug.
-- Add more URI parser test cases.
--
-- Revision 1.3  2003/02/27 08:59:53  graham
-- Separate URI parser from main URI module
--
-- Revision 1.2  2003/02/27 00:30:14  graham
-- Syntax code nearly complete, untested
--
-- Revision 1.1  2003/02/20 19:45:07  graham
-- Add URI module and unit tests.
-- Code incomplete.
--
