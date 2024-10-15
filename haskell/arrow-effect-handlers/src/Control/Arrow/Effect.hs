{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RecordWildCards #-}

module Control.Arrow.Effect
  ( module Control.Category,
    module Control.Arrow,
    Eff (..),
    Handler (..),
    handleWith,
    interpret,
    unit,
    ununit,
    assoc,
    unassoc,
  )
where

import Control.Arrow
import Control.Category
import Text.Show.Functions ()
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Misc

unit :: (Arrow a) => a b (b, ())
unit = arr (,())

ununit :: (Arrow a) => a (b, ()) b
ununit = arr fst

assoc :: (Arrow a) => a ((b, c), d) (b, (c, d))
assoc = arr \ ~(~(b, c), d) -> (b, (c, d))

unassoc :: (Arrow a) => a (b, (c, d)) ((b, c), d)
unassoc = arr \ ~(b, ~(c, d)) -> ((b, c), d)

--------------------------------------------------------------------------------
-- Effectful Arrows and Handlers

data Eff op b c where
  Arr :: (b -> c) -> Eff op b c
  Op :: op b c -> Eff op b c
  Comp :: Eff op c d -> Eff op b c -> Eff op b d
  First :: Eff op b c -> Eff op (b, d) (c, d)

-- for debugging
deriving instance (forall i o. Show (op i o)) => Show (Eff op b c)

instance Category (Eff op) where
  id = Arr id
  (.) = Comp

instance Arrow (Eff op) where
  arr = Arr
  first = First

data Handler op a c d = Handler
  { valh :: a c d,
    effh :: forall i o x. op i o -> a (o, x) d -> a (i, x) d
  }

handleWith ::
  forall op a b c d.
  (Arrow a) =>
  Handler op a c d ->
  Eff op b c ->
  a b d
handleWith Handler {..} m = unit >>> run m (ununit >>> valh)
  where
    run :: forall i o x. Eff op i o -> a (o, x) d -> a (i, x) d
    {-
       i  .+++++++. o  .------.        i  .-------. o  .------.
      --->| Arr f |--->|      |       --->| arr f |--->|      |
          '+++++++'    | cont |  ==>      '-------'    | cont |
      ---------------->|      |       ---------------->|      |
       x            x  '------'        x            x  '------'
    -}
    run (Arr f) cont = arr (first f) >>> cont
    {-
                                          .-----------------.
       i  .+++++++. o  .------.        i  |        .------. |
      --->| Eff e |--->|      |       --->|        |      | |
          '+++++++'    | cont |  ==>      | effh e | cont | |
      ---------------->|      |       --->|        |      | |
       x            x  '------'        x  |        '------' |
                                          '-----------------'
    -}
    run (Op e) cont = effh e cont
    {-
                                                     .-------------------.
       i  .++++++++++. o  .------.        i  .+++. j |  .+++. o .------. |
      --->| Comp f g |--->|      |       --->| g |----->| f |-->|      | |
          '++++++++++'    | cont |  ==>      '+++'   |  '+++'   | cont | |
      ------------------->|      |       ---------------------->|      | |
       x               x  '------'        x        x |       x  '------' |
                                                     '-------------------'
    -}
    run (Comp f g) cont = run g (run f cont)
    {-
                                                                .------------------.
      (i,y) .+++++++++. (o,y) .------.       (i,y)   i .+++. o  |   (o,y) .------. |
      =====>| First f |======>|      |       ====+---->| f |--------+====>|      | |
            '+++++++++'       | cont |  ==>       \    '+++'    |  /      | cont | |
      ----------------------->|      |       ------+==============+------>|      | |
       x                   x  '------'        x        (y,x)    |      x  '------' |
                                                                '------------------'
    -}
    run (First f) cont = assoc >>> run f (unassoc >>> cont)

interpret :: (Arrow a) => (forall i o. op i o -> a i o) -> Eff op b c -> a b c
interpret f =
  handleWith Handler {valh = returnA, effh = \e k -> first (f e) >>> k}
