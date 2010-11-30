%-------------------------------=  --------------------------------------------
\chapter{Digital sorting}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.DigitalSort 
> where
> import Data.Array
> import Data.Bits
> import Data.Int

%align 33

> bucketSort			:: (Ix b) => (b, b) -> (a -> b) -> [a] -> [a]
> bucketSort bs key as		=  [ a | b <- elems buckets, a <- reverse b ]
>     where buckets		=  distribute bs [ (key a, a) | a <- as ]
>
> distribute			:: (Ix a) => (a, a) -> [(a, b)] -> Array a [b]
> distribute			=  accumArray (flip (:)) []
>
> radixSort			:: (Ix b) => (b, b) -> [a -> b] -> [a] -> [a]
> radixSort bs keys x		=  foldr (bucketSort bs) x keys

|keys| must satisfy the following property: let $a \leq_i b
\Longleftrightarrow |key|_i\;a \leq |key|_i\;b$ and $a(R\fatsemi S)b
\Longleftrightarrow aRb \vee (a=b \wedge aSb)$, then $(\leq)
\Longleftrightarrow (\leq_1)\fatsemi\ldots\fatsemi(\leq_n)$.

\NB |Word| should be used instead of |Int| since the sign bit is
ignored.

> int32Keys'			:: [Int32 -> Bool]
> int32Keys'			=  [ \i -> testBit i k | k <- [s - 1, s - 2 .. 0] ]
>     where s			=  bitSize (0 :: Int32)
>
> int32RadixSort'		:: [Int32] -> [Int32]
> int32RadixSort'		=  radixSort (False, True) int32Keys'

|shiftR| does not work properly, that's why |32 - 24| instead of |24|
is used below.

> int32Keys			:: [Int32 -> Int32]
> int32Keys			=  [ \i -> shiftR i (32 - 24) .&. 255
>				   , \i -> shiftR i (32 - 16) .&. 255
>				   , \i -> shiftR i (32 - 8) .&. 255
>				   , \i -> i .&. 255 ]
>
> int32RadixSort		:: [Int32] -> [Int32]
> int32RadixSort		=  radixSort (0, 255) int32Keys
>
