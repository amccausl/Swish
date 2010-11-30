--------------------------------------------------------------------------------
--  $Id: Parse.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Parse
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This Module defines a collection of parsing functions.
--
--  The approach used is based on that in Simon Thompson's book
--  The Craft of Functional Programming, pages 354 et seq.
--
--  The function type for a parser is given by Parser a b (see below)
--  where a is the type of token to be parsed (e.g. Char), and the
--  result is a list of pairs (b,[a]), each corresponding to possible parse,
--  where the first memeber of the pair is the value parsed, and the
--  second is the remaining input sequence following the parsed value.
--
--  A successful parse will generally return a list of one, and an
--  unsuccessful parse returns an empty list.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.Parse
      ( module Swish.HaskellUtils.Parse, isSpace, isAlpha, isDigit, isAlphaNum, isHexDigit )
where

import Data.Char
      ( isSpace, isAlpha, isDigit, isAlphaNum, isHexDigit )

type Parser a b = [a] -> [(b,[a])] -- e.g. [Char] -> [(Result,[Char])]

alpha :: String
alpha    = ['a'..'z']++['A'..'Z']

digit :: String
digit    = ['0'..'9']

alphanum :: String
alphanum = alpha++digit

hexdigit :: String
hexdigit = digit++['a'..'f']++['A'..'F']

isOneOf :: Eq a => [a] -> a -> Bool
isOneOf s c = c `elem` s

-- Assemble alternative parses
parseAlt :: Parser a b -> Parser a b -> Parser a b
parseAlt p1 p2 input = p1 input ++ p2 input


-- Select one of two parses, prefering the first.
parseOne :: Parser a b -> Parser a b -> Parser a b
parseOne p1 p2 input
    | not (null first) = first
    | otherwise        = p2 input
    where first = p1 input

-- Parse optional item returning single list, or empty list if absent
parseOptional :: Parser a [b] -> Parser a [b]
parseOptional p1 = parseOne p1 ( parseReturn [] )

-- Parse sequence of values, returning list of pairs
infixr 5 >*>
(>*>) :: Parser a b -> Parser a c -> Parser a (b,c)
(>*>) p1 p2 input =
  [ ((val1,val2),rem2) | (val1,rem1) <- p1 input, (val2,rem2) <- p2 rem1 ]

-- Apply function to raw result of parse to get required value
-- The supplied function must take account of all the possible parse values
parseApply :: Parser a b -> ( b -> c ) -> Parser a c
parseApply p f input = [ (f val,rem) | (val,rem) <- p input ]

-- Function used with parseApply to flatten the pairs returned by
-- >*> into a list
-- e.g. toList (item,list) = item:list
toList :: (a,[a]) -> [a]
toList = uncurry (:)

-- Function used with parseApply to return a value as a singleton list
-- e.g. makeList item = [item]
makeList :: a -> [a]
makeList x = [x]

-- Function used with parseApply to return a value that is a
-- concatenation of the members of a list.
-- e.g. catList ["ab","cd","ef"] = "abcdef"
catList :: [[a]] -> [a]
catList = foldl (++) []

-- Indicate completion of expression (or sub-expression),
-- returning given value
parseReturn :: b -> Parser a b
parseReturn value input = [(value,input)]

-- Parse any number of tokens matching a supplied parse,
-- returning a list of values parsed
-- type Parser a b = [a] -> [(b,[a])] -- e.g. [Char] -> [(Result,[Char])]
parseMany   :: Parser a b -> Parser a [b]
parseMany p =
    parseOne ( ( p >*> (parseMany p) ) `parseApply` toList )
             ( parseReturn [] )

-- Parse a sequence of a token matching t1 followed by
-- any number of tokens matching t2, returning a list of
-- tokens thus matched
parseSequence :: ( a -> Bool , a -> Bool) -> Parser a [a]
parseSequence ( t1, t2 ) =
    ( parseItem t1 >*> parseMany ( parseItem t2 ) )
    `parseApply` toList

-- Parse a single token matching selector t, returning that value
parseItem   :: ( a -> Bool ) -> Parser a a
parseItem t (next:more)
    | t next    = [(next,more)]
    | otherwise = []
parseItem t []  = []

parseWS :: Parser Char String
parseWS = parseMany (parseItem isSpace)

parseAlpha :: Parser Char Char
parseAlpha  =  parseItem isAlpha

parseDigit :: Parser Char Char
parseDigit  =  parseItem isDigit

parseAlphaNum :: Parser Char Char
parseAlphaNum  =  parseItem isAlphaNum

parseHexDigit :: Parser Char Char
parseHexDigit  =  parseItem isHexDigit

-- Parse input, returning list of values (all parsers must be same type)
infixr 5 >:>
(>:>) :: Parser a b -> Parser a [b] -> Parser a [b]
(p1 >:> p2) input =
  [ (val1:val2,rem2) | (val1,rem1) <- p1 input, (val2,rem2) <- p2 rem1 ]

-- concatenate lists returned by parsers p1 p2
infixr 5 >++>
(>++>) :: Parser a [b] -> Parser a [b] -> Parser a [b]
(p1 >++> p2) input =
  [ (val1++val2,rem2) | (val1,rem1) <- p1 input, (val2,rem2) <- p2 rem1 ]

-- skip token matching p1, then use supplied parser p2
skipToken :: Parser a b -> Parser a c -> Parser a c
skipToken p1 p2 input =
  [ res | (_,rem1) <- p1 input, res <- p2 rem1 ]

-- Fail if end of input not here, otherwise return supplied value
parseEnd :: b -> Parser a b
parseEnd v [] = ( parseReturn v ) []
parseEnd _ _  = []

-- Match null input (returning value ())
parseNull :: Parser a ()
parseNull [] = [((),[])]
parseNull _  = []

-- Test if supplied string matches given parser
isValid :: Parser a b -> [a] -> Bool
isValid parser input =
    not ( null ( ( parser >*> parseNull ) input ) )

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
-- $Source: /file/cvsdev/HaskellUtils/Parse.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: Parse.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.14  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.13  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.12  2003/05/20 23:35:28  graham
-- Modified code to compile with GHC hierarchical libraries
--
-- Revision 1.11  2003/03/28 21:50:22  graham
-- Graph equality coded and nearly working
--
-- Revision 1.10  2003/02/27 13:54:30  graham
-- ParseURI module passes unit test
--
-- Revision 1.9  2003/02/27 00:29:53  graham
-- Add additional parse functions for lists of values
--
-- Revision 1.8  2003/02/20 19:44:37  graham
-- Added isValid and parseNull to Pase module.
-- All tests pass.
--
-- Revision 1.7  2003/02/19 20:20:50  graham
-- Some small parser enhancements
--
-- Revision 1.6  2003/02/19 18:45:00  graham
-- Parser unit tests done.
-- Worked out some details for simplified parser construction.
--
-- Revision 1.5  2003/02/13 16:14:14  graham
-- >*> function works
--
-- Revision 1.4  2003/02/13 15:09:47  graham
-- Initial parser tests all pass.
--
-- Revision 1.3  2003/02/13 11:31:18  graham
-- Separate parser tests from parser code
--
-- Revision 1.2  2003/02/07 18:46:07  graham
-- Add new date/time modules
-- Update copyright year
--
-- Revision 1.1  2003/02/02 15:11:15  graham
-- Created new Parsing module
--
--
