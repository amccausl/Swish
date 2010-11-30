{-# OPTIONS -XFlexibleInstances #-}
--------------------------------------------------------------------------------
--  $Id: ErrorM.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  ErrorM
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a Monad for reporting errors.  It is conceived as a
--  very simple extension of Maybe, except that the failure variant caries
--  a reason for failure.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.ErrorM
    ( ErrorM(Error,Result)
    , eitherErrMaybe
    )
where

import Control.Monad
    ( MonadPlus(..) )

------------------------------------------------------------
--  ErrorM
------------------------------------------------------------

-- |Error monad.
--
data ErrorM a = Error String | Result a

-- |Monad instance for Error
instance Monad ErrorM where
    (Result a) >>= f = f a
    (Error e)  >>= _ = Error e
    return     = Result
    fail e     = Error e

-- |MonadPlus instance for Error
instance MonadPlus ErrorM where
    mzero             = Error "No result"
    mplus (Error _) r = r
    mplus r         _ = r

------------------------------------------------------------
--  Either
------------------------------------------------------------

-- |Monad instance for (Either String b)
instance Monad (Either String) where
    (Left a)  >>= _ = Left a
    (Right b) >>= f = f b
    return          = Right
    fail a          = Left a

-- |MonadPlus instance for (Either String b)
instance MonadPlus (Either String) where
    mzero             = Left "No result"
    mplus (Left _) r  = r
    mplus b        _  = b

-- |Map maybe to (Either String) error monad
eitherErrMaybe :: String -> (a->b) -> Maybe a -> Either String b
eitherErrMaybe err f mv = case mv of
    Nothing -> Left  err
    Just v  -> Right (f v)

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
-- $Source: /file/cvsdev/HaskellUtils/ErrorM.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: ErrorM.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.5  2003/12/10 03:48:57  graham
-- SwishScript nearly complete:  BwdChain and PrrofCheck to do.
--
-- Revision 1.4  2003/12/08 23:55:36  graham
-- Various enhancements to variable bindings and proof structure.
-- New module BuiltInMap coded and tested.
-- Script processor is yet to be completed.
--
-- Revision 1.3  2003/12/04 02:53:27  graham
-- More changes to LookupMap functions.
-- SwishScript logic part complete, type-checks OK.
--
-- Revision 1.2  2003/12/03 15:42:53  graham
-- Add instance declaration for MonadPlus
--
-- Revision 1.1  2003/12/01 21:14:39  graham
-- Added module ErrorM
--
