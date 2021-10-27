{-# OPTIONS_GHC -O2                         #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file #-}

module Test2 where

import Test
import Data.Proxy

blah :: ()
blah = requireEmptyClass @(ToTree('[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])) $ Proxy

