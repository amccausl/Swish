%-------------------------------=  --------------------------------------------
\section{Adaptive heap sort}
%-------------------------------=  --------------------------------------------

%include CartesianTree.lhs

%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -
\subsection{Adaptive heap sort}
%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -

%align

> module Swish.HaskellRDF.Sort.AdaptiveHeapSort
> where
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.CartesianTree (BinTree(..), cartesianTree)
> import Swish.HaskellRDF.Sort.HeapSort (Heap(..), leaf, insertBy)
> import Swish.HaskellRDF.Sort.BraunHeap (siftBy, joinBy)

%align 33

> adaptiveHeapSort		:: (Ord a) => [a] -> [a]
> adaptiveHeapSort		=  adaptiveHeapSortBy (<=)

> adaptiveHeapSortBy (<=) as	=  unheap (leaf (cartesianTree as))
>   where
>
>   Leaf      <== _		=  True
>   Node _ a _ <== Node _ b _	=  a <= b
>   Node _ _ _ <== _		=  False

>   unheap Empty		=  []
>   unheap (Bin t hl hr)	=  case t of
>       Node Leaf a Leaf	-> a : unheap (joinBy (<==) hl hr)
>       Node l a Leaf		-> a : unheap (siftBy (<==) l hl hr)
>       Node Leaf a r		-> a : unheap (siftBy (<==) r hl hr)
>       Node l a r		-> a : unheap (insertBy (<==) r $ siftBy (<==) l hl hr)
