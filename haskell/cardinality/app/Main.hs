{-# LANGUAGE TypeApplications #-}

import Data.Card

main :: IO ()
main = do
  print (card @(Maybe ()))
  print (cardOf (Just False))
  let Card c = Left True :: Either Bool Bool
  print c
