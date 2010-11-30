%-------------------------------=  --------------------------------------------
\chapter{Pairing heaps}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.PairingHeap 
> where
> import Swish.HaskellRDF.Sort.LibBase
> import Swish.HaskellRDF.Sort.ListLib (treefold)
> infixr {-"\,"-} \+/

%align 33

Sorting based on pairing heaps \cite[p.~52]{Oka98Pur} performs
extremely well in practice and it combines many virtues: it is
asymptotically optimal (at least |pairingSort|, for |mpPairingSort|
which is based on multi-pass pairing heaps no tight theoretical bounds
are known), it is lazy and I conjecture that it adapts to the input.
However, to the best of my knowledge this has not been shown. On the
negative side, it is not stable which is typical for sorting algorithms
based on priority queues.

> data PairingHeap a            =  Empty
>                               |  Node a [PairingHeap a]

\NB The constructor |Empty| is only used on the top-level, it never
appears below a |Node|.

> leaf				:: a -> PairingHeap a
> leaf a                  	=  Node a []
>
> (\+/)				:: (Ord a) => PairingHeap a -> PairingHeap a -> PairingHeap a
> (\+/)				=  meldBy (<=)
>
> meldBy			:: Rel a -> PairingHeap a -> PairingHeap a -> PairingHeap a
> meldBy (<=) Empty u		=  u
> meldBy (<=) t@(Node _ _) Empty=  t
> meldBy (<=) t@(Node a ts) u@(Node b us)
>     | a <= b			=  Node a (u : ts)
>     | otherwise		=  Node b (t : us)
>
> pairingSort			:: (Ord a) => [a] -> [a]
> pairingSort			=  pairingSortBy (<=)
>
> pairingSortBy			:: Rel a -> [a] -> [a]
> pairingSortBy (<=)		=  unHeap . meldAll . map leaf
>     where
>     (\+/)			=  meldBy (<=)

Different variants of pairing heaps differ in the implementation of
|meldAll|.

>     meldAll []		=  Empty
>     meldAll [t]		=  t
>     meldAll (t1 : t2 : ts)	=  (t1 \+/ t2) \+/ meldAll ts

Note that subsequent trees are first paired using |meld|, hence the
name of the data structure.

>     unHeap Empty		=  []
>     unHeap (Node a ts)	=  a : unHeap (meldAll ts)

What about the running time? Fredman et al~\cite{FSS86Pai} show that
|meld| and |splitMin| run in $O(\log n)$ amortized time. Hence we have
$O(n\log n)$ worst case behaviour. \NB Chris Okasaki has developed a
persistent variant of pairing heaps~\cite{Oka96Fun} which might be
worth trying, as well.

The function |meldAll| corresponds to |foldr meld empty . pairfold
meld|. Alternatively, one can make repeated passes over the trees using
|treefold meld empty|.

> mpPairingSort			:: (Ord a) => [a] -> [a]
> mpPairingSort			=  mpPairingSortBy (<=)
>
> mpPairingSortBy		:: Rel a -> [a] -> [a]
> mpPairingSortBy (<=)		=  unHeap . meldAll . map leaf
>     where
>     meldAll			=  treefold (meldBy (<=)) Empty
>     unHeap Empty		=  []
>     unHeap (Node a ts)	=  a : unHeap (meldAll ts)

Fredman et al~\cite{FSS86Pai} state that the multipass variant is not
easy to analyse which is certainly true. They only succeeded in proving
an $O(\log n\log\log n/\log\log\log n)$ bound on the amortized time per
heap operation. Hence it is not clear whether |mpPairingSort| is an
$O(n\log n)$ algorithm.
