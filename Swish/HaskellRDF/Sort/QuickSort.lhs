%-------------------------------=  --------------------------------------------
\chapter{Partioning sort}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.QuickSort
> where
> import Swish.HaskellRDF.Sort.MergeSort (mergeSortBy)
> import Data.List
> import Swish.HaskellRDF.Sort.LibBase

%align 33

%-------------------------------=  --------------------------------------------
\section{Some variations of quick sort}
%-------------------------------=  --------------------------------------------
%format qsort1			=  qsort "_1"
%format qsort2			=  qsort "_2"
%format qsort3			=  qsort "_3"

This section lists some variants of quick sort which \emph{cannot be
recommended} for use. The first and probably the most popular of all
appears in \cite[p.~154]{BiW88}, \cite[p.~128]{HinFun92},
\cite[p.~433]{Tho96Has}, and \cite[p.~9]{HPF97Gen}.

> qsort1			:: (Ord a) => [a] -> [a]
> qsort1 []			=  []
> qsort1 (p : as)		=  qsort1 [ a | a <- as, a < p ]
>				++ p : qsort1 [ a | a <- as, p <= a ]

Its main purpose is probably to demonstrate the use and elegancy of
list comprehensions. The definition has, however, several drawbacks
part from the fact that quick sort is not asymptotically optimal.
%
\begin{enumerate}
\item
it traverses the list twice,

\item
it has a space leak: |as| is alive until the second traversal is done
\cite[p.~18]{Bir96Fun},

\item
it uses |(++)| to catenate the results of the recursive calls (note that
|(++)| takes time proportional to the length of its first argument).
\end{enumerate}

The second variant uses the library function |partition| to avoid the
double traversal.

> qsort2			:: (Ord a) => [a] -> [a]
> qsort2 []			=  []
> qsort2 (p : as)		=  qsort2 l ++ p : qsort2 r
>     where (l, r)		=  partition (< p) as

And finally, here is a variant which employs a tail recursive partition
function.

> qsort3			:: (Ord a) => [a] -> [a]
> qsort3 []			=  []
> qsort3 [a]			=  [a]
> qsort3 (p : as)		=  partition [] [] as
>     where
>     partition l r []		=  qsort3 l ++ p : qsort3 r
>     partition l r (a : as)
>         | p <= a 		=  partition l (a : r) as
>	  | otherwise		=  partition (a : l) r as

Note however that |qsort3| is no longer stable since |l| and |r| are in
reverse order.

%-------------------------------=  --------------------------------------------
\section{Paulson's quicksort}
%-------------------------------=  --------------------------------------------

The following code is adpated from \cite[p.~110]{Pau96ML}. The main
difference to |qsort3| is that it uses an accumulating argument to
eliminate the calls to |(++)|.

> quickSort			:: (Ord a) => [a] -> [a]
> quickSort			=  quickSortBy (<=)
>
> quickSortBy			:: Rel a -> [a] -> [a]
> quickSortBy (<=) as		=  qsort as []
>     where
>     qsort []       x		=  x
>     qsort [a]      x		=  a : x
>     qsort (p : as) x		=  partition [] [] as
>         where
>         partition l r []	=  qsort l (p : qsort r x)
>         partition l r (a : as)
>             | p <= a 		=  partition l (a : r) as
>	      | otherwise	=  partition (a : l) r as

%-------------------------------=  --------------------------------------------
\section{Augustsson's stable quicksort}
%-------------------------------=  --------------------------------------------

Neither |qsort3| nor |quickSort| is stable. This is due to the fact
that partition reverses the order of elements (the lists |l| and |r|
are used as a stack). By duplicating the code into a stable and an
anti-stable variant we obtain stability.

> stableQuickSort		:: (Ord a) => [a] -> [a]
> stableQuickSort		=  stableQuickSortBy (<=)
>
> stableQuickSortBy		:: Rel a -> [a] -> [a]
> stableQuickSortBy (<=) as	=  qsortBy (<=) as []
>
> qsortBy			:: Rel a -> [a] -> [a] -> [a]
> qsortBy (<=) []       x 	=  x
> qsortBy (<=) [a]      x	=  a : x
> qsortBy (<=) (p : as) x	=  partition [] [] as
>     where

The function |partition| partitions and sorts the sublists. Note that
|l| and |r| are in reverse order and must be sorted with an anti-stable
sorting.

>     partition l r []		=  rqsortBy (<=) l (p : rqsortBy (<=) r x)
>     partition l r (a : as)
>         | p <= a 		=  partition l (a : r) as
>	  | otherwise		=  partition (a : l) r as

The function |rqsortBy| is as |qsort| but anti-stable, ie it reverses
equal elements (compare the last two equations of |partition|).

> rqsortBy			:: Rel a -> [a] -> [a] -> [a]
> rqsortBy (<=) []       x 	=  x
> rqsortBy (<=) [a]      x	=  a : x
> rqsortBy (<=) (p : as) x	=  partition [] [] as
>     where
>     partition l r []		=  qsortBy (<=) l (p : qsortBy (<=) r x)
>     partition l r (a : as)
>         | a <= p 		=  partition (a : l) r as
>	  | otherwise		=  partition l (a : r) as

%-------------------------------=  --------------------------------------------
\section{Introspective quicksort}
%-------------------------------=  --------------------------------------------

One of the big disadvantages of quick sort is its quadratic worst-case
behaviour. It turns out that it is quite easy to solve this dilemma:
simply limit the recursion depth to a fixed bound, and for subproblems
which exceed the limit use an $\Theta(n\lg n)$ algorithm
\cite{Mus97Int}.

> introSort			:: (Ord a) => [a] -> [a]
> introSort			=  introSortBy (<=)

> introSortBy			:: Rel a -> [a] -> [a]
> introSortBy (<=) as		=  isort (2 * floorLg (length as)) as []
>   where
>   isort 0       as       x	=  mergeSortBy (<=) as ++ x
>   isort (d + 1) []       x	=  x
>   isort (d + 1) [a]      x	=  a : x
>   isort (d + 1) (p : as) x	=  partition [] [] as
>     where
>     partition l r []		=  isort d l (p : isort d r x)
>     partition l r (a : as)
>         | p <= a 		=  partition l (a : r) as
>         | otherwise		=  partition (a : l) r as

Musser recommends a depth bound of |2*floor (lg n)|.

> floorLg                       :: Int -> Int
> floorLg n
>     | n == 1                  =  0
>     | otherwise               =  1 + floorLg (n `div` 2)
