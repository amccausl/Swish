--------------------------------------------------------------------------------
--  $Id: URI.hs,v 1.2 2004/02/02 14:00:39 graham Exp $
--
--  Copyright (c) 2004, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  Network.URI
--  Copyright   :  (c) 2004, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--
--  This module defines functions for handling URIs.  It presents the same
--  interface as the GHC Network.URI module, but is implemented using Parsec
--  rather than a Regex library that is not available with Hugs.
--
--  In addition, four methods are provided for classifying different
--  kinds of URI string (as noted in RFC2396bis):
--      isURI
--      isURIReference
--      isRelativeURI
--      isAbsoluteURI
--
--  The current official reference for URI handling is RFC2396 [1],
--  as updated by RFC 2732 [2].
--
--  These are being merged into RFC2396bis [3], a work-in-progress copy of
--  which is available at the URI indicated.  This document has been used
--  as the primary reference for constructing the URI parser implemented
--  here, and it is intended that there is a direct relationship between
--  the syntax definition in that document and the parser implementation.
--
--  [1] http://www.ietf.org/rfc/rfc2396.txt
--  [2] http://www.ietf.org/rfc/rfc2732.txt
--  [3] http://gbiv.com/protocols/uri/rev-2002/rfc2396bis.html
--      (This implementation based on a version dated Sep-2003,
--      also available as CVS revision 1.64 from
--      http://cvs.apache.org/viewcvs.cgi/ietf-uri/rev-2002/)
--
--  Some of the code has been copied from the GHC implementation, but
--  the parser is replaced with one that performs more complete
--  syntax checking of the URI itself, according to RFC2396bis [3].
--
--------------------------------------------------------------------------------

module {-Network.-} Swish.HaskellUtils.Network.URI
    ( -- * The @URI@ type
      URI(..)
      -- * Parsing a @URI@
    , parseURI                  -- :: String -> Maybe URI
      -- * Testing URI categories
    , isURI, isURIReference, isRelativeURI, isAbsoluteURI
    , isIPv6address, isIPv4address
    , testURIReference
      -- * Computing relative @URI@s
    , relativeTo                -- :: URI -> URI -> Maybe URI
      -- * Operations on @URI@ strings
      -- | support for putting strings into URI-friendly
      -- escaped format and getting them back again.
      -- This can't be done transparently, because certain characters
      -- have different meanings in different kinds of URI.
    , reserved, unreserved
    , isAllowedInURI, unescapedInURI    -- :: Char -> Bool
    , escapeChar                -- :: (Char->Bool) -> Char -> String
    , escapeString              -- :: String -> (Char->Bool) -> String
    , unEscapeString            -- :: String -> String
    )
where

import Numeric( showIntAtBase )

import Data.Char( ord, chr, isHexDigit, isSpace )

{- in Prelude???
import Text.Parsec
    ( GenParser(..), ParseError(..)
    , parse, (<|>), (<?>), try
    , option, many, count, notFollowedBy, lookAhead
    , char, satisfy, oneOf, string, letter, digit, hexDigit, eof
    )
-}
import Text.ParserCombinators.Parsec

------------------------------------------------------------
--  The URI datatype
------------------------------------------------------------

-- |Represents a general universal resource identifier using
--  its component parts.
--
--  For example, for the URI
--
--  >   http://www.haskell.org/ghc?query#frag
--
--  the components are:
--
data URI = URI
    { scheme    :: String   -- ^ @http@
    , authority :: String   -- ^ @www.haskell.org@
    , path      :: String   -- ^ @\/ghc@
    , query     :: String   -- ^ @query@
    , fragment  :: String   -- ^ @frag@
    }

instance Show URI where
    showsPrec _ uri = uriToString uri

------------------------------------------------------------
--  Parse a URI
------------------------------------------------------------

-- |Turn a string into a @URI@.
--  Returns @Nothing@ if the string is not a valid URI.
--
parseURI :: String -> Maybe URI
parseURI uristr = case parseAll uriReference "" uristr of
        Left  _ -> Nothing
        Right u -> Just u

isURI :: String -> Bool
isURI = isValidParse uri

isURIReference :: String -> Bool
isURIReference = isValidParse uriReference

isRelativeURI :: String -> Bool
isRelativeURI = isValidParse relativeUri

isAbsoluteURI :: String -> Bool
isAbsoluteURI = isValidParse absoluteUri

isIPv6address :: String -> Bool
isIPv6address = isValidParse ipv6address

isIPv4address :: String -> Bool
isIPv4address = isValidParse ipv4address

isValidParse :: UriParser a -> String -> Bool
isValidParse parser uristr = case parseAll parser "" uristr of
        -- Left  e -> error (show e)
        Left  _ -> False
        Right u -> True

testURIReference :: String -> String
testURIReference uristr = show (parseAll uriReference "" uristr)

parseAll :: UriParser a -> String -> String -> Either ParseError a
parseAll parser filename uristr = parse newparser filename uristr
    where
        newparser =
            do  { res <- parser
                ; eof
                ; return res
                }

------------------------------------------------------------
--  URI parser body based on Parsec elements and combinators
------------------------------------------------------------

--  Parser parser type.
--  Currently
type UriParser a = GenParser Char () a

--  Relative and absolute forms
--
--  (Note, per RFC2396bis, fragment id is part of the full URI form)
--
--  RFC2396bis, section 4.1

uriReference :: UriParser URI
uriReference = uri <|> relativeUri

--  RFC2396bis, section 4.2

relativeUri :: UriParser URI
relativeUri =
    do  { (ua,up) <- hierPart
        ; uq <- option "" ( do { string "?" ; uquery    } )
        ; uf <- option "" ( do { string "#" ; ufragment } )
        ; return $ URI
            { scheme    = ""
            , authority = ua
            , path      = up
            , query     = uq
            , fragment  = uf
            }
        }

--  RFC2396bis, section 4.3

absoluteUri :: UriParser URI
absoluteUri =
    do  { us <- uscheme
        ; (ua,up) <- hierPart
        ; uq <- option "" ( do { string "?" ; uquery    } )
        ; return $ URI
            { scheme    = us
            , authority = ua
            , path      = up
            , query     = uq
            , fragment  = ""
            }
        }

--  RFC2396bis, section 3

uri :: UriParser URI
uri =
    do  { us <- try uscheme
        ; (ua,up) <- hierPart
        ; uq <- option "" ( do { string "?" ; uquery    } )
        ; uf <- option "" ( do { string "#" ; ufragment } )
        ; return $ URI
            { scheme    = us
            , authority = ua
            , path      = up
            , query     = uq
            , fragment  = uf
            }
        }

hierPart :: UriParser (String,String)
hierPart = netPath <|> absPath <|> relPath

netPath :: UriParser (String,String)
netPath =
    do  { try (string "//")
        ; ua <- uauthority
        ; (_,up) <- option ("","") absPath
        ; return (ua,up)
        }

absPath :: UriParser (String,String)
absPath =
    do  { char '/'
        ; up <- pathSegments
        ; return ("",'/':up)
        }

relPath :: UriParser (String,String)
relPath =
        do  { try uscheme               -- RFC2356bis, section 4.1
            ; fail "Scheme name in relative path"
            }
    <|>
        do  { up <- pathSegments
            ; return ("",up)
            }

--  RFC2396bis, section 3.1

uscheme :: UriParser String
uscheme =
    do  { s <- oneThenMany uriAlphaChar (alphanum <|> oneOf "+-.")
        ; char ':'
        ; return s
        }

--  RFC2396bis, section 3.2

uauthority :: UriParser String
uauthority =
    do  { uu <- option "" (try userinfo)
        ; uh <- option "" host
        ; up <- option "" port
        ; return $ uu++uh++up
        }

userinfo :: UriParser String
userinfo =
    do  { uu <- many (uchar ";:&=+$,")
        ; char '@'
        ; return (concat uu ++"@")
        }

host :: UriParser String
host = ipv6reference <|> try ipv4address <|> hostname

ipv6reference :: UriParser String
ipv6reference =
    do  { char '['
        ; ua <- ipv6address
        ; char ']'
        ; return $ "[" ++ ua ++ "]"
        }

ipv6address :: UriParser String
ipv6address =
        try ( do
                { a2 <- count 6 h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ concat a2 ++ a3
                } )
    <|> try ( do
                { string "::"
                ; a2 <- count 5 h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ "::" ++ concat a2 ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 0
                ; string "::"
                ; a2 <- count 4 h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ concat a2 ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 1
                ; string "::"
                ; a2 <- count 3 h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ concat a2 ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 2
                ; string "::"
                ; a2 <- count 2 h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ concat a2 ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 3
                ; string "::"
                ; a2 <- h4c
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ a2 ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 4
                ; string "::"
                ; a3 <- ls32
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 5
                ; string "::"
                ; a3 <- h4
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::" ++ a3
                } )
    <|> try ( do
                { a1 <- opt_n_h4c_h4 6
                ; string "::"
                -- ; lookAhead $ char ']'
                ; return $ a1 ++ "::"
                } )
    <?> "IPv6 address"

opt_n_h4c_h4 :: Int -> UriParser String
opt_n_h4c_h4 n = option "" $
    do  { a1 <- countMinMax 0 n h4c
        ; a2 <- h4
        ; return $ concat a1 ++ a2
        }

ls32 :: UriParser String
ls32 =  try ( do
                { a1 <- h4c
                ; a2 <- h4
                ; return (a1++a2)
                } )
    <|> ipv4address

h4c :: UriParser String
h4c = try $
    do  { a1 <- h4
        ; char ':'
        ; notFollowedBy (char ':')
        ; return $ a1 ++ ":"
        }

h4 :: UriParser String
h4 = countMinMax 1 4 uriHexDigitChar

ipv4address :: UriParser String
ipv4address =
    do  { a1 <- decOctet ; char '.'
        ; a2 <- decOctet ; char '.'
        ; a3 <- decOctet ; char '.'
        ; a4 <- decOctet
        ; return $ a1++"."++a2++"."++a3++"."++a4
        }

decOctet :: UriParser String
decOctet =
    do  { a1 <- countMinMax 1 3 uriDigitChar
        ; if read a1 > 255 then
            fail "Decimal octet value too large"
          else
            return a1
        }

hostname :: UriParser String
hostname =
    do  { a1 <- domainlabel
        ; a2 <- dqualified
        ; return $ a1 ++ a2
        }

dqualified :: UriParser String
dqualified =
    do  { a1 <- many $ try (
            do  { char '.'
                ; a2 <- domainlabel
                ; return ('.':a2)
                } )
        ; a3 <- option "" (string ".")
        ; return $ concat a1 ++ a3
        }

domainlabel :: UriParser String
domainlabel =
    do  { a1 <- alphanum
        ; a2 <- countMinMax 0 62 (alphanum <|> char '-')
        ; if (not $ null a2) && (last a2 == '-') then
            fail "Domain label ends with '-'"
          else
            return $ a1:a2
        }
    <?> "Domain label"

alphanum :: UriParser Char
alphanum = uriAlphaChar <|> uriDigitChar

port :: UriParser String
port =
    do  { char ':'
        ; p <- many uriDigitChar
        ; return (':':p)
        }

--  RFC2396bis, section 3.3

pathSegments :: UriParser String
pathSegments =
    do  { s1 <- segment
        ; s2 <- many $
            do  { char '/'
                ; s3 <- segment
                ; return ('/':s3)
                }
        ; return $ s1 ++ concat s2
        }

segment :: UriParser String
segment =
    do  { ps <- many pchar
        ; return $ concat ps
        }

pchar :: UriParser String
pchar = uchar ";:@&=+$,"

-- helper function for pchar and friends
uchar :: String -> UriParser String
uchar extras =
        do { c <- satisfy unreserved ; return [c] }
    <|> escaped
    <|> do { c <- oneOf extras ; return [c] }


--  RFC2396bis, section 3.4

uquery :: UriParser String
uquery =
    do  { ss <- many $ uchar (";:@&=+$,"++"/?")
        ; return $ concat ss
        }

--  RFC2396bis, section 3.5

ufragment :: UriParser String
ufragment =
    do  { ss <- many $ uchar (";:@&=+$,"++"/?")
        ; return $ concat ss
        }

--  RFC2396bis, section 2.4.1

escaped :: UriParser String
escaped =
    do  { char '%'
        ; h1 <- uriHexDigitChar
        ; h2 <- uriHexDigitChar
        ; return $ ['%',h1,h2]
        }

--  Imports from RFC 2234

uriAlphaChar :: UriParser Char
uriAlphaChar = letter

uriDigitChar :: UriParser Char
uriDigitChar = digit

uriHexDigitChar :: UriParser Char
uriHexDigitChar = hexDigit

--  Additional parser combinators for common patterns

oneThenMany :: GenParser t s a -> GenParser t s a -> GenParser t s [a]
oneThenMany p1 pr =
    do  { a1 <- p1
        ; ar <- many pr
        ; return (a1:ar)
        }

countMinMax :: Int -> Int -> GenParser t s a -> GenParser t s [a]
countMinMax m n p | m > 0 =
    do  { a1 <- p
        ; ar <- countMinMax (m-1) (n-1) p
        ; return (a1:ar)
        }
countMinMax _ n _ | n <= 0 = return []
countMinMax _ n p = option [] $
    do  { a1 <- p
        ; ar <- countMinMax 0 (n-1) p
        ; return (a1:ar)
        }

------------------------------------------------------------
--  Reconstruct a URI string
------------------------------------------------------------
--
--  Turn a URI into a string.
--
--  Algorithm from part 7, sec 5.2, RFC 2396
--
uriToString :: URI -> ShowS
uriToString URI { scheme=scheme
                , authority=authority
                , path=path
                , query=query
                , fragment=fragment
                } =
    append  ":"  scheme    .
    prepend "//" authority .
    append  ""   path      .
    prepend "?"  query     .
    prepend "#"  fragment
    where
        prepend pre  "" rest = rest
        prepend pre  s  rest = pre ++ s ++ rest
        append  post "" rest = rest
        append  post s  rest = s ++ post ++ rest

------------------------------------------------------------
--  Character classes
------------------------------------------------------------

-- |Returns 'True' if the character is a \"reserved\" character in a
--  URI.  To include a literal instance of one of these characters in a
--  component of a URI, it must be escaped.
--
--  RDF2396bis: section 2.2
--
reserved :: Char -> Bool
reserved c = c `elem` "/?#[];:@&=+$,"

-- |Returns 'True' if the character is an \"unreserved\" character in
--  a URI.  These characters do not need to be escaped in a URI.  The
--  only characters allowed in a URI are either 'reserved',
--  'unreserved', or an escape sequence (@%@ followed by two hex digits).
--
--  RDF2396bis: section 2.3
--
unreserved :: Char -> Bool
unreserved c = (c >= 'A' && c <= 'Z')
        || (c >= 'a' && c <= 'z')
        || (c >= '0' && c <= '9')
        || mark c
    -- NOTE: can't use isAlphaNum etc. because these deal with ISO 8859
    -- (and possibly Unicode!) chars.
    -- [[[Above was a comment originally in GHC Network/URI.hs:
    --    when IRIs are introduced then most codepoints above 128(?) should
    --    be treated as unreserved, and higher codepoints for letters should
    --    certainly be allowed.
    -- ]]]

-- |Returns 'True' if the character is a \"mark\" character.
--
--  RDF2396bis: section 2.3
--
mark :: Char -> Bool
mark c = c `elem` "-_.!~*'()"

-- | Returns 'True' if the character is allowed in a URI.
--
isAllowedInURI :: Char -> Bool
isAllowedInURI c = reserved c || unreserved c || c == '%' -- escape char

-- | Returns 'True' if the character is allowed unescaped in a URI.
--
unescapedInURI :: Char -> Bool
unescapedInURI c = reserved c || unreserved c

------------------------------------------------------------
--  Escape sequence handling
------------------------------------------------------------

-- |Escape character if supplied predicate is not satisfied,
--  otherwise return character as singleton string.
--
escapeChar :: (Char->Bool) -> Char -> String
escapeChar p c
    | p c       = [c]
    | otherwise = '%' : myShowHex (ord c) ""
    where
        myShowHex :: Int -> ShowS
        myShowHex n r =  case showIntAtBase 16 (toChrHex) n r of
            []  -> "00"
            [c] -> ['0',c]
            cs  -> cs
        toChrHex d
            | d < 10    = chr (ord '0' + fromIntegral d)
            | otherwise = chr (ord 'A' + fromIntegral (d - 10))

-- |Can be used to make a string valid for use in a URI.
--
escapeString
    :: String           -- ^ the string to process
    -> (Char->Bool)     -- ^ a predicate which returns 'False'
                        --   if the character should be escaped
    -> String           -- the resulting URI string
escapeString s p = concatMap (escapeChar p) s

-- |Turns all instances of escaped characters in the string back
--  into literal characters.
unEscapeString :: String -> String
unEscapeString [] = ""
unEscapeString ('%':x1:x2:s) | isHexDigit x1 && isHexDigit x2 =
    chr (hexDigit x1 * 16 + hexDigit x2) : unEscapeString s
    where
        hexDigit c
            | c >= 'A' && c <= 'F' = ord c - ord 'A' + 10
            | c >= 'a' && c <= 'f' = ord c - ord 'a' + 10
            | otherwise            = ord c - ord '0'
unEscapeString (c:s) = c : unEscapeString s

------------------------------------------------------------
-- Resolving a relative URI relative to a base URI
------------------------------------------------------------

-- |Returns a new @URI@ which represents the value of the
--  first @URI@ interpreted as relative to the second @URI@.
--  For example:
--
--  > "foo" `relativeTo` "http://bar.org/" = "http://bar.org/foo"
--
--  Algorithm from sec 5.2, RFC 2396
--
relativeTo :: URI -> URI -> Maybe URI
ref `relativeTo` base =
  -- ref has a scheme name, use it in its entirety.  Otherwise inherit
  -- the scheme name from base.
  if ref_scheme    /= ""  then Just ref else

  -- ref has an authority - we're done.  Otherwise inherit the authority.
  if ref_authority /= ""  then Just ref{scheme = base_scheme} else

  -- ref has an absolute path, we're done.
  if not (null ref_path) && head ref_path == '/'
        then Just ref{scheme = base_scheme,
                      authority = base_authority} else

  -- relative path...
  let new_path = munge (dropLastComponent base_path ++ ref_path) []
  in if isErrorPath new_path
        then Nothing
        else Just ref{scheme = base_scheme,
                      authority = base_authority,
                      path = new_path}
  where
        URI{
          scheme    = ref_scheme,
          authority = ref_authority,
          path      = ref_path,
          query     = _ref_query,
          fragment  = _ref_fragment
         } = ref

        URI{
          scheme    = base_scheme,
          authority = base_authority,
          path      = base_path,
          query     = _base_query,
          fragment  = _base_fragment
         } = base

        munge [] [] = ""
        munge [] ps = concat (reverse ps)
        munge ('.':'/':s)     ps     = munge s ps
        munge ['.']           ps     = munge [] ps
        munge ('.':'.':'/':s) (p:ps) | p /= "/" = munge s ps
        munge ['.','.']       (p:ps) = munge [] ps
        munge s               ps     = munge rest' (p':ps)
                where (p,rest) = break (=='/') s
                      (p',rest') = case rest of
                                        '/':r -> (p++"/",r)
                                        r     -> (p,r)

        dropLastComponent = reverse . dropWhile (/= '/') . reverse

        isErrorPath ('/':'.':'.':'/':_) = True
        isErrorPath _ = False

stripLeadingWS, stripTrailingWS, stripWS :: String -> String
stripLeadingWS  = dropWhile isSpace
stripTrailingWS = reverse . stripLeadingWS . reverse
stripWS         = stripLeadingWS . stripTrailingWS

--------------------------------------------------------------------------------
--
--  Copyright (c) 2004, G. KLYNE.  All rights reserved.
--
--  This is free software; you can redistribute it and/or modify
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
--  along with this software; if not, write to:
--    The Free Software Foundation, Inc.,
--    59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
--
--------------------------------------------------------------------------------
-- $Source: /file/cvsdev/HaskellUtils/Network/URI.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: URI.hs,v $
-- Revision 1.2  2004/02/02 14:00:39  graham
-- Fix optional host name in URI.  Add test cases.
--
-- Revision 1.1  2004/01/27 21:13:45  graham
-- New URI module and test suite added,
-- implementing the GHC Network.URI interface.
--
--
