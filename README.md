# polysemy-check

[![Hackage](https://img.shields.io/hackage/v/polysemy-check.svg?logo=haskell&label=polysemy-check)](https://hackage.haskell.org/package/polysemy-check)

## Dedication

> Success is most often achieved by those who don't know that failure is
> inevitable.
>
> --Coco Chanel

## Overview

`polysemy-check` is a little package that integrates
[`polysemy`](https://hackage.haskell.org/package/polysemy) with
[`QuickCheck`](https://hackage.haskell.org/package/QuickCheck). It allows you to
prove the equivalence of effects (see `prepropLaw`), the equivalence of
interpreters (`prepropEquivalent`), and that two effects don't affect one
another (`prepropCommutative`). These three things are about the only problems
you could possibly run into with Polysemy --- and now you won't.

In addition `polysemy-check` provides lots of machinery to help avoid
boilerplate, such as free `Arbitrary` instances for effects.


## Usage

`polysemy-check` requires a `Show` and `GenericK` instance for every effect
you'd like to run tests over.

```haskell
{-# LANGUAGE TemplateHaskell #-}

import Polysemy
import Polysemy.Check

data Stack m a where
  Push :: Int -> Stack m ()
  Pop  :: Stack m (Maybe Int)
  Size :: Stack m Int

deriving instance Show (Stack m a)
makeSem ''Stack
deriveGenericK ''Stack
```


## Examples

Check the [test
suite](https://github.com/polysemy-research/polysemy-check/tree/master/test).

