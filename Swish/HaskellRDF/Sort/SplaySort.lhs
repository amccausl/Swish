%-------------------------------=  --------------------------------------------
\chapter{Splay sort}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.SplaySort 
> where
> import Swish.HaskellRDF.Sort.LibBase

%align 33

Sorting on the basis on splay trees has most of the desired features:
is asymptotically optimal, stable and it adapts to the input. In fact,
it has been conjectured \cite{MEP96Spl} that it is optimatically
adaptive to all accepted measures of presortedness. The following code
is due to Chris Okasaki \cite[p.~46]{Oka98Pur}.

> data SplayTree a 		=  Empty
>				|  Bin (SplayTree a) a (SplayTree a)
>
> insertBy			:: Rel a -> a -> SplayTree a -> SplayTree a
> insertBy (<=) a t		=  Bin lt a ge
>    where (lt, ge)		=  partBy (<=) a t

\NB |lt| means \U{l}ess \U{t}han and |ge| means \U{g}reater \U{e}qual.

> partBy			:: Rel a -> a -> SplayTree a -> (SplayTree a, SplayTree a)
> partBy (<=) k Empty		=  (Empty, Empty)
> partBy (<=) k t@(Bin l a r)
>    | k <= a			=  case l of
>         Empty			-> (Empty, t)
>         Bin ll la lr
>             | k <= la		-> let (lt, ge) = partBy (<=) k ll in (lt, Bin ge la (Bin lr a r))
>             | otherwise	-> let (lt, ge) = partBy (<=) k lr in (Bin ll la lt, Bin ge a r)
>     | otherwise		=  case r of
>         Empty			-> (t, Empty)
>         Bin rl ra rr
>             | k <= ra		-> let (lt, ge) =  partBy (<=) k rl in (Bin l a lt, Bin ge ra rr)
>             | otherwise	-> let (lt, ge) =  partBy (<=) k rr in (Bin (Bin l a rl) ra lt, ge)

\NB Throughout the library great care is taken to ensure that the
relative order of equal elements is preserved. This is most easily
accomplished if the order of the arguments to a function reflects the
original order within the input. Consider, for example, the definition
of |insertBy|: on the left hand side |a| appears before |t|, on the
right hand side |a| appears before |ge| which may contain elements
equal to |a|. Thus, the relative order of equal elements is preserved.
That said, it is probably clear which we use |foldr| instead of |foldl|
for building trees.

> inorder			:: SplayTree a -> [a]
> inorder t			=  traverse t []
>     where
>     traverse Empty x		=  x
>     traverse (Bin l a r) x	=  traverse l (a : traverse r x)
>
> splaySort			:: (Ord a) => [a] -> [a]
> splaySort			=  splaySortBy (<=)
>
> splaySortBy			:: Rel a -> [a] -> [a]
> splaySortBy (<=)		=  inorder . foldr (insertBy (<=)) Empty

