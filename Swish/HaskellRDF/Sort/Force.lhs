%-------------------------------=  --------------------------------------------
\section{Hyper-strict evaluation}
%-------------------------------=  --------------------------------------------

%align

> module Swish.HaskellRDF.Sort.Force 
> where

%align 33

Vollst"andige Auswertung.

> class Force a where
>     force			:: a -> ()
>
>     force a			=  a `seq` ()

> instance Force Bool
> instance Force Char
> instance Force Int
> instance Force Integer
> instance Force Double
>
> instance (Force a) => Force [a] where
>     force []			=  ()
>     force (a : as)		=  force a `seq` force as
