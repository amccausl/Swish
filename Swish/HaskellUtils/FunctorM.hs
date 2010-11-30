--------------------------------------------------------------------------------
--  $Id: FunctorM.hs,v 1.2 2004/01/13 17:12:08 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  FunctorM
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a monadic functor class, that allows a monadic
--  computation to be performed, functor-style, over some container
--  structure.  The advantage of this compared with a normal functor
--  is that it allows values to be accumulated from the computation
--  (in a Monad instance) at the same time as (optionally) applying
--  transformations to each of the contained values.
--
--  Acknowledgement:  based on a message by Tomasz Zielonka sent to
--  the Haskell mailing list on 4 June 2003.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.FunctorM
    ( FunctorM(..)
    )
where

class FunctorM t where
    fmapM  :: Monad m => (a -> m b) -> (t a -> m (t b))
    -- Try to generalise accumulating values?
    -- fmapQM :: Monad m => m b -> (b -> a -> m b) -> (t a -> m b)
    fmapM_ :: Monad m => (a -> m b) -> (t a -> m ())
    fmapM_ f t = fmapM f t >> return ()

instance FunctorM [] where
    fmapM  = mapM
    fmapM_ = mapM_

{-  Another example:

data Arc lb = Arc { asubj, apred, aobj :: lb }
    deriving (Eq, Show)

instance Functor Arc where
    fmap f (Arc s p o) = Arc (f s) (f p) (f o)

instance FunctorM Arc where
    -- fmapM :: (lb -> m l2) -> Arc lb -> m (Arc l2)
    fmapM f (Arc s p o) =
        do  { s' <- f s
            ; p' <- f p
            ; o' <- f o
            ; return $ Arc s' p' o'
            }

-}

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
-- $Source: /file/cvsdev/HaskellUtils/FunctorM.hs,v $
-- $Author: graham $
-- $Revision: 1.2 $
-- $Log: FunctorM.hs,v $
-- Revision 1.2  2004/01/13 17:12:08  graham
-- Complete functionality of AccumulateM, using functional dependencies
-- in the MonadAccum type class.
--
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.3  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.2  2003/06/12 00:49:04  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
-- Revision 1.1  2003/06/10 17:34:29  graham
-- Create FunctorM module
--
