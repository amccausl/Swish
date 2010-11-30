%-------------------------------=  --------------------------------------------
\section{List library}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.ListLib 
> where

%align 33

> simple			:: [a] -> Bool
> simple []			=  True
> simple [a]			=  True
> simple (a1 : a2 : as)		=  False

> halve				:: [a] -> ([a], [a])
> halve as			=  splitAt (length as `div` 2) as

> repSplit			:: [Int] -> [a] -> [[a]]
> repSplit ns []		=  []
> repSplit [] xs		=  [xs]
> repSplit (n : ns) xs		=  ys : repSplit ns zs
>   where (ys, zs)		=  splitAt n xs

> copy				:: [a] -> [a]
> copy				=  concat . repeat

> interleave			:: [a] -> [a] -> [a]
> interleave [] y		=  y
> interleave (a:x) y		=  a : interleave y x

> uninterleave			:: [a] -> ([a], [a])
> uninterleave []		=  ([], [])
> uninterleave [a]		=  ([a], [])
> uninterleave (a1 : a2 : as)	=  (a1 : odds, a2 : evens)
>     where (odds, evens)	=  uninterleave as

%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -
\subsection{folds}
%- - - - - - - - - - - - - - - -=  - - - - - - - - - - - - - - - - - - - - - -

Here is yet another colleague of |foldr| and |foldl|: |foldm|
constructs a balanced expression tree.

> foldm				:: (a -> a -> a) -> a -> [a] -> a
> foldm (*) e []		=  e
> foldm (*) e x			=  fst (rec (length x) x)
>     where rec 1 (a:x)		=  (a, x)
>           rec n x		=  (a * b, z)
>               where m		=  n `div` 2
>                     (a, y)	=  rec (n - m) x 
>                     (b, z)	=  rec m       y

> gfoldm			:: a -> (b -> a) -> (a -> a -> a) -> [b] -> a
> gfoldm e f (*) []		=  e
> gfoldm e f (*) x		=  fst (rec (length x) x)
>     where rec 1 (a:x)		=  (f a, x)
>           rec n x		=  (a * b, z)
>               where m		=  n `div` 2
>                     (a, y)	=  rec (n - m) x 
>                     (b, z)	=  rec m       y

Jon's |treefold|. In a sense |foldm| works top-down and |treefold|
works bottom-up.

> treefold			:: (a -> a -> a) -> a -> [a] -> a
> treefold (*) e []		=  e
> treefold (*) e [a]		=  a
> treefold (*) e (a:b:x)	=  treefold (*) e (a * b : pairfold (*) x)

> pairfold			:: (a -> a -> a) -> [a] -> [a]
> pairfold (*) (a:b:x)		=  a * b : pairfold (*) x
> pairfold (*) x		=  x -- here |x| will have fewer than two 

Note that |foldm| and |treefold| construct different trees: |foldm|
returns a Braun tree while |treefold| returns a tree of the form
\[	
    |t1 * (t2 * (.. (tn-1 * tn) ..))|
\]
where the |ti|'s are complete binary trees in decreasing size. The size
of the trees corresponds to the binary decomposition of the input
length.

"`Inverse"' Funktion zum Preorder-Durchlauf.

> prefold			:: (a -> b -> b -> b) -> b -> [a] -> b
> prefold f e as		=  fst (rec (length as) as)
>     where rec 0 as		=  (e, as)
>           rec (n + 1) []	=  error "rec"
>           rec (n + 1) (a : as)=  (f a l r, as2)
>               where m		=  n `div` 2
>                     (l, as1)	=  rec (n - m) as
>                     (r, as2)	=  rec m       as1

> perms				:: [a] -> [[a]]
> perms []			=  [ [] ]
> perms (a:x)			=  [ z | y <- perms x, z <- insertions a y ]
>
> insertions			:: a -> [a] -> [[a]]
> insertions a []		=  [ [a] ]
> insertions a x@(b:y)		=  (a:x) : [ b:z | z <- insertions a y ]

> spaces			:: Int -> [Char]
> spaces n			=  replicate (max n 0) ' '

> cjustify, ljustify, rjustify	:: Int -> String -> String
> cjustify                      =  cjustifyWith ' '
> ljustify n s			=  s ++ spaces (n - length s)
> rjustify n s			=  spaces (n - length s) ++ s

> indent			:: Int -> String -> String
> indent n s			=  spaces n ++ s

> cjustifyWith			:: a -> Int -> [a] -> [a]
> cjustifyWith c n s            =  replicate l c ++ s ++ replicate r c
>     where m                   =  n - length s
>           l                   =  m `div` 2
>           r                   =  m - l
