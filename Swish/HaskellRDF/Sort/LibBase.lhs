%-------------------------------=  --------------------------------------------
\section{Base functions and types}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.LibBase 
> where

%align 33

> type Rel a			=  a -> a -> Bool

> data OptPair a b		=  Null
>				|  Pair a b

> ordered			:: (Ord a) => [a] -> Bool
> ordered			=  orderedBy (<=)

> orderedBy			:: Rel a -> [a] -> Bool
> orderedBy (<=) []		=  True
> orderedBy (<=) (a : as)	=  ordered a as
>   where ordered a1 []		=  True
>         ordered a1 (a2 : as)	=  a1 <= a2 && ordered a2 as
