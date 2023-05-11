{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

import Control.Monad
import Control.Monad.Trans.MSF.Except
import Data.Function
import Data.MonadicStreamFunction
import Oath
import System.IO

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetBuffering stdout NoBuffering
  let freq = 10
  reactimate proc () -> do
    -- There might be a better way of modularizing periodic sampling
    maybeInput <- getChar `every` (1000000 `div` freq) -< ()
    n <- count -< ()
    let pulse1s = n `mod` freq == 0
        startStop = maybeInput == Just ' '
        reset = maybeInput == Just '\n'
    time <- stopWatch -< (pulse1s, startStop, reset)
    onChange (\t -> putStr $ replicate 20 '\b' ++ format t) -< time

format :: Int -> String
format sec = shows h . showChar ':' . shows m . showChar ':' . shows s $ ""
  where
    (hm, s) = sec `divMod` 60
    (h, m) = hm `divMod` 60

data Mode = Run | Pause

stopWatch :: Monad m => MSF m (Bool, Bool, Bool) Int
stopWatch =
  feedback' 0 $ foreverDSwitch Pause \case
    Pause ->
      proc ((_, startStop, reset), prevTime) -> do
        let time = if reset then 0 else prevTime
        let nextMode = if startStop then Just Run else Nothing
        returnA -< (time, nextMode)
    Run ->
      proc ((pulse1s, startStop, _), prevTime) -> do
        let time = prevTime + if pulse1s then 1 else 0
        let nextMode = if startStop then Just Pause else Nothing
        returnA -< (time, nextMode)

-- Utilities

feedback' :: Monad m => b -> MSF m (a, b) b -> MSF m a b
feedback' b sf = feedback b $ sf >>^ \b' -> (b', b')

foreverDSwitch :: Monad m => c -> (c -> MSF m a (b, Maybe c)) -> MSF m a b
foreverDSwitch c f = flip fix c \g c' -> dSwitch (f c') g

onChange :: (Eq a, Monad m) => (a -> m ()) -> MSink m a
onChange f = proc a -> do
  a' <- iPre Nothing -< Just a
  arrM id -< when (a' /= Just a) (f a)

every :: IO a -> Int -> MSF IO () (Maybe a)
m `every` dur = constM $ evalOath $ timeout dur (oath m) <* delay dur
