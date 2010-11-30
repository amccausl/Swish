%-------------------------------=  --------------------------------------------
\chapter{Braun heaps}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.BraunHeap
> where
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.ListLib (prefold)
> import Swish.HaskellRDF.Sort.HeapSort (Heap(..), leaf, insertBy)

%align 33

%-------------------------------=  --------------------------------------------
\section{Top-down heap sort}
%-------------------------------=  --------------------------------------------

Here is a variant of heap sort due to Paulson \cite[p. 160]{Pau96ML}
which follows the original more closely. Recall that imperative
implementations of heap sort use an implicit representation of binary
heaps ie the binary tree is embedded in an array. For a functional
explanation we step backward and represent an array by a binary tree.
The original heap sort uses left-complete trees. We use Braun
trees~\cite[p. 154]{Pau96ML} instead. However, every implementation of
functional arrays would do. We could generalize the following to an
array-based implementation of priority queues.

The construction of the heap works as before.  The second phase mimics
the imperative version: the smallest element (ie the leftmost) is
replaced by an arbitrary element (usually the rightmost) which is
sifted down the heap. Here we replace the root (ie the leftmost) by the
leftmost leaf (ie an element in the rear part of the array). Both
|splitLeft| and |sift| employ the fact that their arguments are Braun
trees.

> unHeapBy			:: Rel a -> Heap a -> [a]
> unHeapBy (<=) Empty		=  []
> unHeapBy (<=) (Bin a l r)	=  a : unHeapBy (<=) (joinBy (<=) l r)
>
> joinBy			:: Rel a -> Heap a -> Heap a -> Heap a
> joinBy (<=) l r		=  case splitLeft l of
>     Null			-> Empty
>     Pair a l'			-> siftBy (<=) a r l'
>
> splitLeft			:: Heap a -> OptPair a (Heap a)
> splitLeft Empty		=  Null
> splitLeft (Bin a l r)		=  case splitLeft l of
>     Null			-> Pair a Empty		-- |r == Empty|
>     Pair b l'			-> Pair b (Bin a r l')

The recursion scheme is dual to that of |insert|: the element is always
deleted into the left subtree (which is possibly bigger). Additionally,
the left and the right branch are interchanged (in case both subtrees
have the same size).

> siftBy			:: Rel a -> a -> Heap a -> Heap a -> Heap a
> siftBy (<=)			=  sift
>   where
>   sift a Empty r		=  leaf a		-- |r == Empty|
>   sift a l@(Bin b _ _) Empty				-- |l == leaf b|
>       | a <= b		=  Bin a l Empty
>       | otherwise		=  Bin b (leaf a) Empty
>   sift a l@(Bin a1 l1 r1) r@(Bin a2 l2 r2)
>       | a <= a1 && a <= a2	=  Bin a l r
>       | a1 <= a2		=  Bin a1 (sift a l1 r1) r
>       | otherwise		=  Bin a2 l (sift a l2 r2)

We do not use the |sift| function defined in |HeapSort| because |sift|
on Braun trees is slightly simpler. Note, however, that |sift| makes a
redundant comparison if |a2 < a <= a1|.

> braunSort			:: (Ord a) => [a] -> [a]
> braunSort			=  braunSortBy (<=)
>
> braunSortBy			:: Rel a -> [a] -> [a]
> braunSortBy (<=)		=  unHeapBy (<=) . foldr (insertBy (<=)) Empty

%-------------------------------=  --------------------------------------------
\section{Bottom-up heap sort}
%-------------------------------=  --------------------------------------------

The bottom-up variant is straightforward and a true transliteration of
Williams' heap sort apart from the fact that we use Braun trees instead
of left-complete trees.

> bottomUpBraunSort		:: (Ord a) => [a] -> [a]
> bottomUpBraunSort		=  bottomUpBraunSortBy (<=)
>
> bottomUpBraunSortBy		:: Rel a -> [a] -> [a]
> bottomUpBraunSortBy (<=)	=  unHeapBy (<=) . prefold (siftBy (<=)) Empty
