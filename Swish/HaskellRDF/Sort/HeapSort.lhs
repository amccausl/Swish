%-------------------------------=  --------------------------------------------
\chapter{Heap sort}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.HeapSort 
> where
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.ListLib
> import Swish.HaskellRDF.Sort.MergeSort (mergeBy)

%align 33

%-------------------------------=  --------------------------------------------
\section{Top-down heap sort}
%-------------------------------=  --------------------------------------------

It appears that the functional variant of heap sort has been invented
several times. See, for instance, \cite[p.~155]{HinFun92} or
\cite[p.~20]{Bir96Fun}.

Heap sort is based on binary heap ordered trees.

> data Heap a			=  Empty
>				|  Bin a (Heap a) (Heap a)
>
> leaf				:: a -> Heap a
> leaf a			=  Bin a Empty Empty

The top-down variant works by repeatedly inserting elements into an
empty initial tree.

> insertBy			:: Rel a -> a -> Heap a -> Heap a
> insertBy (<=) a Empty		=  leaf a
> insertBy (<=) a (Bin b l r)
>     | a <= b			=  Bin a (insertBy (<=) b r) l
>     | otherwise		=  Bin b (insertBy (<=) a r) l

Repeated |insert|'s constructs a so-called Braun tree (|size r <= size
l <= size r+1| holds for each |Bin l a r|). This guarantees a worst
case running time of $O(n\log n)$ for |heapSort|. The recursion scheme
is typical for Braun trees:  the element is always inserted into the
right subtree (which is possibly smaller). Additionally, the left and
the right branch are interchanged (in case both subtrees have the same
size). This implies, however, that |heapSort| is not stable.

> unHeapBy			:: Rel a -> Heap a -> [a]
> unHeapBy (<=) Empty		=  []
> unHeapBy (<=) (Bin a l r)	=  a : mergeBy (<=) (unHeapBy (<=) l)
>				                    (unHeapBy (<=) r)
>
> heapSort			:: (Ord a) => [a] -> [a]
> heapSort			=  heapSortBy (<=)
>
> heapSortBy			:: Rel a -> [a] -> [a]
> heapSortBy (<=)		=  unHeapBy (<=) . foldr (insertBy (<=)) Empty


The function |unheap| resorts to |merge| which probably not in the
spirit of the original heap sort by Williams (see also
\cite[p.~21]{Bir96Fun} where |meld| is called combine). Instead we can
combine the two subheaps into one.

> unHeap			:: (Ord a) => Heap a -> [a]
> unHeap Empty			=  []
> unHeap (Bin a l r)		=  a : unHeap (meld l r)
>
> meld				:: (Ord a) => Heap a -> Heap a -> Heap a
> meld Empty t'			=  t'
> meld t@(Bin _ _ _) Empty	=  t
> meld t@(Bin a l r) t'@(Bin a' l' r')
>        | a <= a'		=  Bin a  (meld l r) t'
>        | otherwise		=  Bin a' t (meld l' r')

This variant of |unHeap| also clarifies the relationship to merge
sort. First note that |meld| is closely related to |merge|. We have
%
\begin{eqnarray*}
    |toOrdList (meld t u)|
        & = & |merge (toOrdList t) (toOrdList u)| \enskip.
\end{eqnarray*}
%
Thus

> heapSort'			:: (Ord a) => [a] -> [a]
> heapSort'			=  unHeap . gfoldm Empty leaf meld

is structurally equivalent to |mergeSort| (ie it performs the same
comparisons during the sorting process). In essence, this shows that it
is unlikely that heap sort is faster than merge sort. As a final remark
note that |heapSort'| is stable and lazy.

%-------------------------------=  --------------------------------------------
\section{Bottom-up heap sort}
%-------------------------------=  --------------------------------------------

It is well known that a heap can be constructed in linear time.  We
have already seen a simple method, namely |gfoldm empty leaf meld|!
The classical solution employs a function termed |sift|. Functionally
speaking, |sift| is a smart constructor for binary heaps, ie it
combines an element and two heaps into a single heap.
{\setlength{\lwidth}{\lwidth + 1cm}

> siftBy			:: Rel a -> a -> Heap a -> Heap a -> Heap a
> siftBy (<=)			=  sift
>   where
>   sift a Empty Empty		=  leaf a
>   sift a Empty r@(Bin _ _ _)	=  siftr a Empty r
>   sift a l@(Bin _ _ _) Empty	=  siftl a l Empty
>   sift a l@(Bin b _ _) r@(Bin c _ _)
>       | b <= c		=  siftl a l r
>       | otherwise		=  siftr a l r
>
>   siftl a Empty r		=  error "siftl"
>   siftl a l@(Bin b ll lr) r
>       | a <= b		=  Bin a l r
>       | otherwise		=  Bin b (sift a ll lr) r
> 
>   siftr a l Empty		=  error "siftr"
>   siftr a l r@(Bin b rl rr)
>       | a <= b		=  Bin a l r
>       | otherwise		=  Bin b l (sift a rl rr)

Note that |sift| does not change the structure of the subheaps. We
could be more reluctant and replace |siftr| by |siftl|.  Unfortunately,
|sift| is not stable, ie the relative order of elements is not
preserved.}

> bottomUpHeapSort		:: (Ord a) => [a] -> [a]
> bottomUpHeapSort		=  bottomUpHeapSortBy (<=)
>
> bottomUpHeapSortBy		:: Rel a -> [a] -> [a]
> bottomUpHeapSortBy (<=)	=  unHeapBy (<=) . prefold (siftBy (<=)) Empty

To see what |prefold| does, consider the call |prefold Bin Empty as|.
The result is a Braun tree the preorder traversal of which yields
|as|.  An alternative algorithm which constructs a tree whose
\technical{level-order} traversal is equal to the original sequence is
given in \cite[p.~22]{Bir96Fun}.
