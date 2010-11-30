{-# OPTIONS -XMultiParamTypeClasses #-}
{-# OPTIONS -XFunctionalDependencies #-}
{-# OPTIONS -XFlexibleInstances #-}

--------------------------------------------------------------------------------
--  $Id: AccumulateM.hs,v 1.3 2004/01/22 19:53:46 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  AccummulateM
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This module defines a monadic accumulator type.  The plan is that it be
--  used in conjunction with FunctorM and similar constructs to accumulate
--  some or all of the values visited.
--
--  Using a monad of type Accumulator, which wraps some type 'c' and is
--  also declared to be an instance of MonadAccum Accumulator c e, for some e,
--  then foldM can be used to accumulate values of type e with an initial
--  value of type c with the instance-supplied growVal method.
--
--  This module also declares accumulator instances for Int, Integer and list
--  datatypes.
--
--  This is all very well, but rather unnecessary:  it is just as easy, and
--  more standard (hence easier for other Haskell programmers to follow),
--  to use a state monad with a nullary return type; e.g.
--     execsState (stateMonadExpr) initialState
--  which returns the final state value.
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.AccumulateM
    ( Accumulator(..) )
where

import Control.Monad
    ( foldM )


class (Monad m) => MonadAccum m c e | m c -> e where
    growVal :: c -> e -> m c
    reapVal :: m c -> c

data Accumulator c = Accumulator c deriving (Eq, Show)

instance Monad Accumulator where
    (Accumulator v) >>= k  = k v
    return v               = Accumulator v

instance MonadAccum Accumulator Int Int where
    growVal n m             = Accumulator (n+m)
    reapVal (Accumulator n) = n

instance MonadAccum Accumulator Integer Integer where
    growVal n m             = Accumulator (n+m)
    reapVal (Accumulator n) = n

instance MonadAccum Accumulator [v] v where
    growVal vs v             = Accumulator (v:vs)
    reapVal (Accumulator vs) = vs


--  Tests
addVal :: Int -> Int -> (Accumulator Int)
addVal m n = Accumulator (n+m)

testList  = [1,2,3,4,5,6] :: [Int]
testList1 = [1,2,3,4,5,6] :: [Integer]
testList2 = "plugh"

test1 = foldM addVal 0 testList
test2 = Accumulator 0
test3 = (Accumulator 0) >>= addVal 1
test4 = (Accumulator 5) >>= addVal 5
test5 = (growVal 3 :: Int -> Accumulator Int) 20
test6 = foldM growVal 0 testList  :: Accumulator Int
test7 = foldM growVal 0 testList1 :: Accumulator Integer
test8 = reapVal (foldM growVal 0  testList  :: Accumulator Int)
test9 = reapVal (foldM growVal [] testList2 :: Accumulator [Char])

test = and
    [ test1 == Accumulator 21
    , test2 == Accumulator 0
    , test3 == Accumulator 1
    , test4 == Accumulator 10
    , test5 == Accumulator 23
    , test6 == Accumulator 21
    , test7 == Accumulator 21
    , test8 == 21
    , test9 == "hgulp"
    ]

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
-- $Source: /file/cvsdev/HaskellUtils/AccumulateM.hs,v $
-- $Author: graham $
-- $Revision: 1.3 $
-- $Log: AccumulateM.hs,v $
-- Revision 1.3  2004/01/22 19:53:46  graham
-- Sync.
--
-- Revision 1.2  2004/01/13 17:12:08  graham
-- Complete functionality of AccumulateM, using functional dependencies
-- in the MonadAccum type class.
--
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.2  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.1  2003/06/12 00:49:04  graham
-- Basic query processor runs test cases OK.
-- Proof framework compiles, not yet tested.
--
