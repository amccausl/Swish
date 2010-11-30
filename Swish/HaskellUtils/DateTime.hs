--------------------------------------------------------------------------------
--  $Id: DateTime.hs,v 1.1 2004/01/13 12:31:24 graham Exp $
--
--  Copyright (c) 2003, G. KLYNE.  All rights reserved.
--  See end of this file for licence information.
--------------------------------------------------------------------------------
-- |
--  Module      :  DateTime
--  Copyright   :  (c) 2003, Graham Klyne
--  License     :  GPL V2
--
--  Maintainer  :  Graham Klyne
--  Stability   :  provisional
--  Portability :  H98
--
--  This Module defines a collection of date/time manipulation functions.
--
--  Date/time value manipulation.
--
--  Date/time can be date-only or time-only
--
--  type DateTime is an instance of built-in classes Eq and Show
--  type DateTime has a constructor that accepts a string in the format
--      defined by RFC 3339.
--      Timezone interpretation is per RFC3339.
--
--------------------------------------------------------------------------------
--
--            year,month,day,hour,min,sec,millisec,timezone
--class (Show a,Eq a) => DateTimeClass a where
--  newDateTime  :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> a
--  toString     :: a -> String
--  size         :: a -> Int
--  toDateTime   :: String -> a
--  toDate       :: String -> a
--  toTime       :: String -> a
--  (==)         :: a -> a -> Bool   -- same date/time
--  (<)        :: a -> a -> Bool   -- first precedes second
--  (+)        :: a -> a -> a  -- advance by time
--  (-)        :: a -> a -> a  -- difference between times
--  dtShow     :: a -> String             -- return string form
--  dtYear       :: a -> Int
--  dtMonth      :: a -> Int
--  dtDay        :: a -> Int
--  dtHour       :: a -> Int
--  dtMinute     :: a -> Int
--  dtSecond     :: a -> Int
--  dtMillisecs  :: a -> Int
--  dtTimezone   :: a -> Int                -- time zone offset in minutes
--
--------------------------------------------------------------------------------

module Swish.HaskellUtils.DateTime where

data DateTime
  = DateTime Int Int Int Int Int Int Int Int

instance Eq DateTime where
  d1 == d2 = simpleEq ( normTZ d1 ) ( normTZ d2 )

instance Show DateTime where
  show dt = dtShow dt

instance Ord DateTime where
  dt1 <  dt2  = simpleLT ( normTZ dt1 ) ( normTZ dt2 )
  dt1 >  dt2  = dt2 < dt1
  dt1 <= dt2  = (dt1 < dt2)||(dt1==dt2)
  dt1 >= dt2  = (dt2 < dt1)||(dt1==dt2)

leapYear :: Int -> Bool
leapYear year
  | ( year `mod` 4 == 0 ) &&
    not ( ( year `mod` 100 == 0 ) &&
          not ( year `mod` 400 == 0 ) ) = True
  | otherwise                           = False

daysInMonth :: Int -> Int -> Int
daysInMonth month year
  | month==1   = 31  --Jan
  | month==2   = if leapYear year then 29 else 28 --Feb
  | month==3   = 31  --Mar
  | month==4   = 30  --Apr
  | month==5   = 31  --May
  | month==6   = 30  --Jun
  | month==7   = 31  --Jul
  | month==8   = 31  --Aug
  | month==9   = 30  --Sep
  | month==10  = 31  --Oct
  | month==11  = 30  --Nov
  | month==12  = 31  --Dec
  | otherwise  = 0

validJulianDate :: Int -> Int -> Int -> Bool
validJulianDate yr mo da
  | yr < 1900                = False
  | mo > 12                  = False
  | da > (daysInMonth mo yr) = False
  | otherwise                = True

toJulianDate1 :: DateTime -> Int
toJulianDate1 (DateTime y m d _ _ _ _ _) = toJulianDate y m d

toJulianDate :: Int -> Int -> Int -> Int
toJulianDate year month day
--  | not (validJulianDate year month day) = -1
  | year==1900 && month<=2               = if month==2 then day + 30 else day - 1
  | month>=3                             = toJD1 (year-1900) (month-3) (day)
  | otherwise                            = toJD1 (year-1901) (month+9) (day)
  where
    toJD1 :: Int -> Int -> Int -> Int
    toJD1 year month day
      = ( (1461*year) `div` 4 ) -
        (year `div` 100) +
        ((year+300) `div` 400) +
        ( ( (153*month) + 2 ) `div` 5 ) +
        day + 58

fromJulianDate:: Int -> DateTime
fromJulianDate jdate
  | jdate <= 58 = fromJD1 jdate
  | otherwise   = fromJD2 jdate
  where
    fromJD1 :: Int -> DateTime
    fromJD1 jdate
      | jdate<=30 = (DateTime 1900 1 (jdate+1 ) 0 0 0 0 0)
      | otherwise = (DateTime 1900 2 (jdate-30) 0 0 0 0 0)

    fromJD2 :: Int -> DateTime
    fromJD2 j
      = DateTime y2 m2 d1 0 0 0 0 0
      where
--          t1 = (400*(j+((j+36467)`div`36525)-((j+109517)`div`dc))) - 23638 -- 1/400-days from 1900-02-28 [t]
          t1 = (400*
                    (j
               +((4*(j+36465))`div`146097)
                  -((j+109513)`div`146097))) - 23638 -- 1/400-days from 1900-02-28 [t]
          dc = 146100                                -- days in cycle period (400 years) = 1/400-days in year
          t2 = ( ( t1 `mod` dc ) `div` 400 )*5 + 2   -- fifth-days into year, +2                      [j3]
          d1 = ( t2 `mod` 153 ) `div` 5 + 1          -- day of month (magic number 153)               [d]
          m1 = t2 `div` 153                          -- month Mar=0 -> Feb=11                         [j4]
          m2 = if m1 <= 9 then m1+3 else m1-9        -- correct month to Jan=1 -> Dec=12              [m]
          y1 = t1 `div` dc + 1900                    -- year from 1900-02-28
          y2 = if m1 <= 9 then y1   else y1+1        -- correct year for month wrap-around
          -- 36525  = days/century, not counting century adjustments
          -- 109517 = 146100 * (1900-1600)/400 - 58
          -- 23238  = 58*400 + 38  ???   38=152/4 ??

{-          -- this code works for dates before 2100 only
          t1 = (4*j) - 233                           -- quarter-days from 1900-02-28
          dc = 1461                                  -- days in cycle period (4 years) = quarter-days in year
          t2 = ( ( t1 `mod` dc ) `div` 4 )*5 + 2     -- fifth-days into year, +2
          d1 = ( t2 `mod` 153 ) `div` 5 + 1          -- day of month (magic number 153)
          m1 = t2 `div` 153                          -- month Mar=0 -> Feb=11
          m2 = if m1 <= 9 then m1+3 else m1-9        -- correct month to Jan=1 -> Dec=12
          y1 = t1 `div` dc + 1900                    -- year from 1900-02-28
          y2 = if m1 <= 9 then y1   else y1+1        -- correct year for month wrap-around
-}

date :: Int -> Int -> Int -> DateTime
date y m d = DateTime y m d 0 0 0 0 0

time :: Int -> Int -> Int -> Int -> Int -> DateTime
time h m s ms z = DateTime 0 0 0 h m s ms z

dtYear       :: DateTime -> Int
dtMonth      :: DateTime -> Int
dtDay        :: DateTime -> Int
dtHour       :: DateTime -> Int
dtMinute     :: DateTime -> Int
dtSecond     :: DateTime -> Int
dtMillisecs  :: DateTime -> Int
dtTimezone   :: DateTime -> Int                -- time zone offset in minutes
dtYear      ( DateTime x _ _ _ _ _ _ _ ) = x
dtMonth     ( DateTime _ x _ _ _ _ _ _ ) = x
dtDay       ( DateTime _ _ x _ _ _ _ _ ) = x
dtHour      ( DateTime _ _ _ x _ _ _ _ ) = x
dtMinute    ( DateTime _ _ _ _ x _ _ _ ) = x
dtSecond    ( DateTime _ _ _ _ _ x _ _ ) = x
dtMillisecs ( DateTime _ _ _ _ _ _ x _ ) = x
dtTimezone  ( DateTime _ _ _ _ _ _ _ x ) = x

lenFix     :: String -> Int -> String
lenFix inStr newLen
  | length inStr >= newLen  = inStr
  | otherwise               = lenFix ('0':inStr) newLen

showTZ     :: Int -> String
showTZ tz
  | tz<0         = "-" ++ showTZabs ( -tz )
  | tz==0        = showTZabs ( tz )
  | otherwise    = "+" ++ showTZabs ( tz )

showTZabs  :: Int -> String
showTZabs tz
  | tz==0        = "Z"
  | otherwise    = lenFix ( show ( tz `div` 60 ) ) 2 ++  ":" ++
                   lenFix ( show ( tz `mod` 60 ) ) 2

showTime :: DateTime -> String
showTime ( DateTime yr mo da hr mi se ms tz )
  | ms==0     = lenFix ( show hr ) 2 ++  ":" ++
                lenFix ( show mi ) 2 ++  ":" ++
                lenFix ( show se ) 2
  | otherwise = lenFix ( show hr ) 2 ++ ":" ++
                lenFix ( show mi ) 2 ++ ":" ++
                lenFix ( show se ) 2 ++ "." ++
                lenFix ( show ms ) 3

showDate :: DateTime -> String
showDate ( DateTime yr mo da hr mi se ms tz )
  = lenFix ( show yr ) 4 ++ "-" ++
    lenFix ( show mo ) 2 ++ "-" ++
    lenFix ( show da ) 2

dtShow     :: DateTime -> String             -- return string form
dtShow ( DateTime yr mo da hr mi se ms tz )
  = showDate ( DateTime yr mo da hr mi se ms tz ) ++ "T" ++
    showTime ( DateTime yr mo da hr mi se ms tz ) ++ showTZ tz

carryMins :: DateTime -> DateTime
carryMins ( DateTime yr mo da hr mi se ms tz )
  | newhrs >= 24 = carryHours ( DateTime yr mo da newhrs (mi`mod`60) se ms tz )
  | otherwise    = ( DateTime yr mo da newhrs (mi`mod`60) se ms tz )
  where
    newhrs = (hr+(mi`div`60))

carryHours :: DateTime -> DateTime
carryHours ( DateTime yr mo da hr mi se ms tz )
  = ( DateTime y m d (hr`mod`24) mi se ms tz )
  where
    (DateTime y m d _ _ _ _ _) = fromJulianDate ((toJulianDate yr mo da)+ (hr`div`24))

normTZ :: DateTime -> DateTime
normTZ ( DateTime yr mo da hr mi se ms tz )
  = carryMins ( DateTime yr mo da hr (mi-tz) se ms 0 )
--  = addMinutes (-tz) ( DateTime yr mo da hr mi se ms tz )

{- another way -}

addMilliSecs addms ( DateTime yr mo da hr mi se ms tz )
    | totms < 1000 = DateTime yr mo da hr mi se totms tz
    | otherwise    = addSeconds addse ( DateTime yr mo da hr mi se newms tz )
    where
        totms = (ms+addms)
        newms = totms `mod` 1000
        addse = totms `div` 1000

addSeconds addse ( DateTime yr mo da hr mi se ms tz )
    | totse < 60 = DateTime yr mo da hr mi totse ms tz
    | otherwise  = addMinutes addmi ( DateTime yr mo da hr mi newse ms tz )
    where
        totse = (se+addse)
        newse = totse `mod` 60
        addmi = totse `div` 60

addMinutes addmi ( DateTime yr mo da hr mi se ms tz )
    | totmi < 60 = DateTime yr mo da hr totmi se ms tz
    | otherwise  = addHours addhr ( DateTime yr mo da hr newmi se ms tz )
    where
        totmi = (mi+addmi)
        newmi = totmi `mod` 60
        addhr = totmi `div` 60

addHours addhr ( DateTime yr mo da hr mi se ms tz )
    | tothr < 24 = DateTime yr mo da tothr mi se ms tz
    | otherwise  = addDays addda ( DateTime yr mo da newhr mi se ms tz )
    where
        tothr = (hr+addhr)
        newhr = tothr `mod` 24
        addda = tothr `div` 24

addDays addda ( DateTime yr mo da hr mi se ms tz )
    = DateTime newyr newmo newda hr mi se ms tz
    where
        -- newdate = fromJulianDate (toJulianDate yr mo (da+addda) )
        -- newyr   = dtYear newdate
        -- newmo   = dtMonth newdate
        -- newda   = dtDay newdate
        DateTime newyr newmo newda _ _ _ _ _ = fromJulianDate ( (toJulianDate yr mo da)+addda )

{- another way -}

simpleEq :: DateTime -> DateTime -> Bool
--simpleEq ( DateTime yr1 mo1 da1 hr1 mi1 se1 ms1 tz1 ) ( DateTime yr2 mo2 da2 hr2 mi2 se2 ms2 tz2 ) = ( ( yr1 mo1 da1 hr1 mi1 se1 ms1 tz1 ) == ( yr2 mo2 da2 hr2 mi2 se2 ms2 tz2 ) )
simpleEq ( DateTime yr1 mo1 da1 hr1 mi1 se1 ms1 tz1 ) ( DateTime yr2 mo2 da2 hr2 mi2 se2 ms2 tz2 ) = ( ( yr1 == yr2 ) && ( mo1 == mo2 ) && ( da1 == da2 ) && ( hr1 == hr2 ) && ( mi1 == mi2 ) && ( se1 == se2 ) && ( ms1 == ms2 ) && ( tz1 == tz2 ) )

simpleLT :: DateTime -> DateTime -> Bool
simpleLT ( DateTime yr1 mo1 da1 hr1 mi1 se1 ms1 tz1 ) ( DateTime yr2 mo2 da2 hr2 mi2 se2 ms2 tz2 )
  | (yr1<yr2) = True
  | (yr1==yr2)&&(mo1<mo2) = True
  | (yr1==yr2)&&(mo1==mo2)&&(da1<da2) = True
  | (yr1==yr2)&&(mo1==mo2)&&(da1==da2)&&(hr1<hr2) = True
  | (yr1==yr2)&&(mo1==mo2)&&(da1==da2)&&(hr1==hr2)&&(mi1<mi2) = True
  | (yr1==yr2)&&(mo1==mo2)&&(da1==da2)&&(hr1==hr2)&&(mi1==mi2)&&(se1<se2) = True
  | (yr1==yr2)&&(mo1==mo2)&&(da1==da2)&&(hr1==hr2)&&(mi1==mi2)&&(se1==se2)&&(ms1<ms2) = True
  | otherwise = False

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
-- $Source: /file/cvsdev/HaskellUtils/DateTime.hs,v $
-- $Author: graham $
-- $Revision: 1.1 $
-- $Log: DateTime.hs,v $
-- Revision 1.1  2004/01/13 12:31:24  graham
-- Move modules from HaskellRDF to HaskellUtils project
--
-- Revision 1.23  2003/09/24 18:50:52  graham
-- Revised module format to be Haddock compatible.
--
-- Revision 1.22  2003/06/03 19:24:13  graham
-- Updated all source modules to cite GNU Public Licence
--
-- Revision 1.21  2003/02/21 14:35:10  ronan
-- Minor performance tweaks.
--
-- Revision 1.20  2003/02/17 13:15:13  ronan
-- fromJulianDate passed exhaustive 2299-3601
--
-- Revision 1.19  2003/02/15 13:44:29  graham
-- Added test output to file.
-- Still a bug around 2300-03-01
--
-- Revision 1.18  2003/02/15 12:00:30  graham
-- Fix 400-year roll-over bug
--
-- Revision 1.17  2003/02/14 20:33:43  ronan
-- fromJulianDate works.
--
-- Revision 1.16  2003/02/14 20:31:44  ronan
-- fromJulianDate works.
--
-- Revision 1.14  2003/02/14 10:22:06  graham
-- fromJulianDate works for dates before 2100
--
-- Revision 1.13  2003/02/13 13:01:55  graham
-- Added some test cases for fromJulianDate and comparison
-- with date rollover.  Currently not working.
--
-- Revision 1.12  2003/02/13 10:26:01  ronan
-- Minor tweaks to performance. Still passes tests.
--
-- Revision 1.11  2003/02/12 12:26:43  ronan
-- fromJulianDate now also working perfectly.
--
-- Revision 1.10  2003/02/12 11:57:02  ronan
-- Julian date stuff PERFECT!!!
--
-- Revision 1.9  2003/02/11 18:08:43  graham
-- Added loads of new test cases
-- Moved Julian date test cases to DateTimeTest
--
-- Revision 1.8  2003/02/11 16:04:28  ronan
-- Put Julian in DateTime and added normTZ functionality. Vaguely tested (2 cases).
--
-- Revision 1.7  2003/02/11 12:02:34  graham
-- Minor updates
-- Add some Julian date test cases
--
-- Revision 1.6  2003/02/11 10:47:17  ronan
-- Work on DateTime. (==) works as intended. Julian date work done, needs testing.
--
-- Revision 1.5  2003/02/10 14:21:57  ronan
-- Tests very bodged, but working. Show working to a good standard. (==) replaced with (===) for now. Next step: timezone correction.
--
-- Revision 1.2  2003/02/09 09:20:37  ronan
-- Working on DateTime in Haskell. Not working. Yet.
--
-- Revision 1.1  2003/02/07 18:46:07  graham
-- Add new date/time modules
-- Update copyright year
--
