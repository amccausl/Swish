%-------------------------------=  --------------------------------------------
\chapter{Sorting by merging}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.MergeSort 
> where
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.ListLib

> infixr {-"\,"-} `merge`, \+/

%align 33

> sort				:: (Ord a) => [a] -> [a]
> sort				=  bottomUpMergeSort

%-------------------------------=  --------------------------------------------
\section{Top-down merge sort}
%-------------------------------=  --------------------------------------------

The archetypical functional sorting algorithm is without any doubt
merge sort. It follows the divide and conquer scheme: the input list is
split into two halves, both are sorted recursively and the results are
finally merged together.

> merge				:: (Ord a) => [a] -> [a] -> [a]
> merge				=  mergeBy (<=)
>
> (\+/)				:: (Ord a) => [a] -> [a] -> [a]
> (\+/)				=  mergeBy (<=)
>
> mergeBy			:: Rel a -> [a] -> [a] -> [a]
> mergeBy (<=)			=  merge
>     where
>     merge [] bs		=  bs
>     merge as@(_ : _) []	=  as
>     merge as@(a : as') bs@(b : bs')
>         | a <= b		=  a : merge as' bs
>	  | otherwise		=  b : merge as  bs'
>
> mergeSort			:: (Ord a) => [a] -> [a]
> mergeSort			=  mergeSortBy (<=)
>
> mergeSortBy			:: Rel a -> [a] -> [a]
> mergeSortBy (<=) as
>     | simple as		=  as
>     | otherwise		=  mergeBy (<=) (mergeSortBy (<=) as1)
>				                (mergeSortBy (<=) as2)
>     where (as1, as2)		=  halve as

Since the divide phase takes $\Theta(n\log n)$ time, |mergeSort| is
not lazy: |head . mergeSort| has a running time of $\Theta(n\log n)$.

%-------------------------------=  --------------------------------------------
\section{Bottom-up merge sort}
%-------------------------------=  --------------------------------------------

The function |bottomUpMergeSort| improves the divide phase to
$\Theta(n)$ and is consequently asymptotically optimal, stable, and
lazy, but alas not in any way adaptive.

> bottomUpMergeSort		:: (Ord a) => [a] -> [a]
> bottomUpMergeSort		=  bottomUpMergeSortBy (<=)
>
> bottomUpMergeSortBy		:: Rel a -> [a] -> [a]
> bottomUpMergeSortBy (<=)	=  gfoldm [] (\a -> [a]) (mergeBy (<=))

%-------------------------------=  --------------------------------------------
\section{Straight merge sort}
%-------------------------------=  --------------------------------------------

Both |mergeSort| and |bottomUpMergeSort| take $\Theta(n\log n)$
irrespective of the presortedness of the input. If we replace the test
|simple| by |ordered| we obtain an adaptive variant which is optimal
with respect to the measure |Runs| and adaptive wrt |Inv| and |Rem|
\cite[p.~449]{ECW92Sur}.

> straightMergeSort		:: (Ord a) => [a] -> [a]
> straightMergeSort		=  straightMergeSortBy (<=)

> straightMergeSortBy		:: Rel a -> [a] -> [a]
> straightMergeSortBy (<=) as
>     | orderedBy (<=) as	=  as
>     | otherwise		=  mergeBy (<=) (straightMergeSortBy (<=) as1)
>				                (straightMergeSortBy (<=) as2)
>     where (as1, as2)		=  halve as

\Todo{To adapt to ascending as well as descending sequences we could
reverse the sublists in every step and apply Augustson's
stable/anti-stable trick.}

%-------------------------------=  --------------------------------------------
\section{Odd-even merge sort}
%-------------------------------=  --------------------------------------------

If we use a different partioning scheme, |uninterleave| instead of
|halve|, we obtain an adaptive variant which is optimal wrt |Dis = Max|
\cite[p.~450]{ECW92Sur}.

> oddEvenMergeSort		:: (Ord a) => [a] -> [a]
> oddEvenMergeSort		=  oddEvenMergeSortBy (<=)
>
> oddEvenMergeSortBy		:: Rel a -> [a] -> [a]
> oddEvenMergeSortBy (<=) as
>     | orderedBy (<=) as	=  as
>     | otherwise		=  mergeBy (<=) (oddEvenMergeSortBy (<=) as1)
>						(oddEvenMergeSortBy (<=) as2)
>     where (as1, as2)		=  uninterleave as

Unfortunately, |oddEvenMergeSort| is no longer stable. Consider, for
instance, |uninterleave [a1, a2, a3] = ([a1, a3], [a2])| and assume
that the three elements are equal. However, |oddEvenMergeSort| can be
improved so that the divide phase takes only linear time. This is left
as an instructive exercise to the reader.

%-------------------------------=  --------------------------------------------
\section{Split sort}
%-------------------------------=  --------------------------------------------

A partioning scheme which adapts to |Rem| was given by Levcopoulos
and Petersson \cite[p.~451]{ECW92Sur} and is based on a method by
Cook and Kim for removing $\Theta(|Rem(as)|)$ elements from a list
|as|, such that an ordered sequence is left over.

The function |lpDivision as| divides its input into three lists |g|,
|s|, and |l| such that |s| is sorted and |g| and |l| have the same
length which is at most |Rem(as)|. The tricky thing is to ensure that
the splitting is performed in a stable way, ie the order in which the
elements in |g| and |l| appear is the same in which they appear in
|as|. Consider the sequence |1 2 5 1 4 3 1 9 2 8 9 1|:
%
\[
\begin{array}{l||l||r}
\text{|g| and |s|} & |l| & |as| \\\hline
|1 2 5| & & |1 4 3 1 9 2 8 9 1| \\
|1 2 [5]| & |1| & |4 3 1 9 2 8 9 1| \\
|1 2 [5] 4| & |1| & |3 1 9 2 8 9 1| \\
|1 2 [5 4]| & |3 1| & |1 9 2 8 9 1| \\
|1 [2 5 4]| & |1 3 1| & |9 2 8 9 1| \\
|1 [2 5 4] 9| & |1 3 1| & |2 8 9 1| \\
|1 [2 5 4 9]| & |2 1 3 1| & |8 9 1| \\
|1 [2 5 4 9] 8| & |2 1 3 1| & |9 1| \\
|1 [2 5 4 9] 8 9| & |2 1 3 1| & |1| \\
|1 [2 5 4 9] 8 [9]| & |1 2 1 3 1| &
\end{array}
\]
The data type |Region| is designed to represent |g| and |s|. Elements
in |g| are grouped to allow for efficient access to the last element in
|s|. For instance, |1 [2 5 4 9] 8 [9]| is essentially represented by |G
(S (G (S Nil 1) [2, 5, 4, 9]) 8) [9]|.

> type Sequ a			=  [a] -> [a]
>
> data Region a			=  Nil
>				|  S (Region a) a
>				|  G (Region a) (Sequ a)
>
> single			:: a -> Sequ a
> single a			=  \x -> a : x
>
> g				:: Region a -> Sequ a -> Region a
> g Nil gs			=  G Nil gs
> g (S s a) gs			=  G (S s a) gs
> g (G s gs1) gs2		=  G s (gs1 . gs2)
>
> lpDivisionBy			:: Rel a -> [a] -> ([a], [a], [a])
> lpDivisionBy (<=) []          =  ([], [], [])
> lpDivisionBy (<=) (a : as)    =  lp (S Nil a) [] as
>     where
>     lp s l []              	=  (g [], reverse s', reverse l)
>         where (g, s')		=  lpPart s
>     lp Nil l (a : as)		=  lp (S Nil a) l as
>     lp s@(G Nil gs) l (a : as)=  lp (S s a) l as
>     lp s@(G (S s' m) gs) l (a : as)
>         | m <= a		=  lp (S s a) l as
>         | otherwise		=  lp (g s' (single m . gs)) (a : l) as
>     lp (G (G _ _) _) _ (_ : _)=  error "lp"
>     lp s@(S s' m) l (a : as)
>         | m <= a		=  lp (S s a) l as
>         | otherwise		=  lp (g s' (single m)) (a : l) as
>
> lpPart			:: Region a -> ([a] -> [a], [a])
> lpPart Nil			=  (id, [])
> lpPart (S s a)		=  (g, a : s')
>     where (g, s')		=  lpPart s
> lpPart (G s gs)		=  (gs . g, s')
>     where (g, s')		=  lpPart s

Unfortunately, the relative order between equal elements in |g ++ s ++ l|
is not the same as in |as|. Hence, |lpMergeSort| is not stable either.

> lpMergeSort			:: (Ord a) => [a] -> [a]
> lpMergeSort			=  lpMergeSortBy (<=)
>
> lpMergeSortBy			:: Rel a -> [a] -> [a]
> lpMergeSortBy (<=) as
>     | simple as		=  as
>     | otherwise		=  mergeBy (<=) (lpMergeSortBy (<=) as1)
>				       (mergeBy (<=) s (lpMergeSortBy (<=) as2))
>     where (as1, s, as2)	=  lpDivisionBy (<=) as

\Todo{To adapt to ascending as well as descending sequences we could
reverse the sublists in every step. \NB stability is already lost.}

%-------------------------------=  --------------------------------------------
\section{Adaptive merge sort}
%-------------------------------=  --------------------------------------------
%format sort1			=  sort "_1"
%format sort2			=  sort "_2"
%format sort3			=  sort "_3"

If we combine |halve|, |uninterleave|, and |lpDivision| we obtain
a sorting algorithm which is adaptive wrt |Exc|, |Dis|, |Inv|, |Rem|,
and |Runs| \cite[p.~451]{ECW92Sur}.

> adaptiveMergeSort		:: (Ord a) => [a] -> [a]
> adaptiveMergeSort		=  adaptiveMergeSortBy (<=)
>
> adaptiveMergeSortBy		:: Rel a -> [a] -> [a]
> adaptiveMergeSortBy (<=)	=  sort1
>     where
>     (\+/)			=  mergeBy (<=)
>
>     sort1 as
>         | simple as		=  as
>         | otherwise		=  sort2 as1 \+/ s \+/ sort2 as2
>         where (as1, s, as2)	=  lpDivisionBy (<=) as
>
>     sort2 as			=  sort3 as1 \+/ sort3 as2
>         where (as1, as2)	=  uninterleave as
>
>     sort3 as			=  sort1 as1 \+/ sort1 as2
>         where (as1, as2)	=  halve as

\Todo{How about reversing the lists in the first step in order to adapt
to descending sequences as well? cf.~\cite[p.~52]{ECW91Pra}}

%-------------------------------=  --------------------------------------------
\section{Natural merge sort}
%-------------------------------=  --------------------------------------------

The function |straightMergeSort| somehow guesses the number of runs. It is
more efficient to group the input into runs beforehand.

> naturalMergeSort		:: (Ord a) => [a] -> [a]
> naturalMergeSort		=  naturalMergeSortBy (<=)
>
> naturalMergeSortBy		:: Rel a -> [a] -> [a]
> naturalMergeSortBy (<=)	=  foldm (mergeBy (<=)) [] . runsBy (<=)
>
> runsBy			:: Rel a -> [a] -> [[a]]
> runsBy (<=) []		=  [[]]
> runsBy (<=) (a : as)		=  upRun a [] as
>     where
>     upRun m r []		=  [reverse (m : r)]
>     upRun m r (a : as)
>         | m <= a		=  upRun a (m : r) as
>         | otherwise		=  reverse (m : r) : upRun a [] as

Natural merge sort was first studied in the context of external
sorting.  The hbc library contains a similar function.

The function |runs| recognized only ascending runs. With little
additional effort we can also detect descending runs.

> symmetricNaturalMergeSort	:: (Ord a) => [a] -> [a]
> symmetricNaturalMergeSort	=  symmetricNaturalMergeSortBy (<=)
>
> symmetricNaturalMergeSortBy	:: Rel a -> [a] -> [a]
> symmetricNaturalMergeSortBy (<=)
>				=  foldm (mergeBy (<=)) [] . upDownRunsBy (<=)
>
> upDownRunsBy			:: Rel a -> [a] -> [[a]]
> upDownRunsBy (<=) []		=  []
> upDownRunsBy (<=) (a : as)	=  upDownRun a as
>     where
>     upDownRun a []		=  [[a]]
>     upDownRun a1 (a2 : as)
>         | a1 <= a2		=  upRun   a2 [a1] as
>         | otherwise		=  downRun a2 [a1] as
>     upRun m r []		=  [reverse (m : r)]
>     upRun m r (a : as)
>         | m <= a		=  upRun a (m : r) as
>         | otherwise		=  reverse (m : r) : upDownRun a as
>
>     downRun m r []		=  [m : r]
>     downRun m r (a : as)
>         | m <= a		=  (m : r) : upDownRun a as
>         | otherwise		=  downRun a (m : r) as

\NB To preserve stability |downRun| uses only \emph{strictly}
decreasing sequences: |[n, n, n-1, n-1, .. 1, 1]| is split into |n|
runs. Does anybody know of a better solution?
