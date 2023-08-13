# Typograms with Zipper

A simpler version of [Typograms](https://google.github.io/typograms/) implemented with the Zipper comonad on 2D vector.

```sh
$ cat typograms/mocks.txt
 .-------------------------.
 |.-----------------------.|
 ||  https://example.com  ||
 |'-----------------------'|
 |                         |
 |+-----------------------+|
 ||    Welcome!           ||
 ||  .-----------------.  ||
 ||  | username        |  ||
 ||  '-----------------'  ||
 ||  .-----------------.  ||
 ||  | *******         |  ||
 ||  '-----------------'  ||
 ||                       ||
 ||  .-----------------.  ||
 ||  |    Sign-up      |  ||
 ||  '-----------------'  ||
 |+-----------------------+|
 '-------------------------'

$ cabal run < typograms/mocks.txt
 ╭-------------------------╮
 |╭-----------------------╮|
 ||  https://example.com  ||
 |╰-----------------------╯|
 |                         |
 |┌-----------------------┐|
 ||    Welcome!           ||
 ||  ╭-----------------╮  ||
 ||  | username        |  ||
 ||  ╰-----------------╯  ||
 ||  ╭-----------------╮  ||
 ||  | *******         |  ||
 ||  ╰-----------------╯  ||
 ||                       ||
 ||  ╭-----------------╮  ||
 ||  |    Sign-up      |  ||
 ||  ╰-----------------╯  ||
 |└-----------------------┘|
 ╰-------------------------╯
```

```haskell
-- Zipper on 2D vector
type Z2 n m a = Store (V.Vector n `Compose` V.Vector m) a

-- 3x3 window
data Window = W
  { ul, u, ur :: Char,
    l, c, r :: Char,
    dl, d, dr :: Char
  }

currWindow :: (KnownNat n, KnownNat m) => Z2 n m Char -> Window
currWindow zz =
  W
    { ul = ix (decr, decr) zz,
      u = ix (decr, pure) zz,
      ur = ix (decr, incr) zz,
      l = ix (pure, decr) zz,
      c = ix (pure, pure) zz,
      r = ix (pure, incr) zz,
      dl = ix (incr, decr) zz,
      d = ix (incr, pure) zz,
      dr = ix (incr, incr) zz
    }
  where
    ix (f, g) = fromMaybe '\0' . experiment (bitraverse f g)
    incr n = succ n <$ guard (n /= maxBound)
    decr n = pred n <$ guard (n /= minBound)

convert :: (KnownNat n, KnownNat m) => Z2 n m Char -> Z2 n m Char
convert = extend (conv . currWindow)
  where
    conv = \case
      W {c = '+', u = '|', l = '-', r = '-', d = '|'} -> '┼'
      W {c = '+', l = '-', r = '-', d = '|'} -> '┬'
      W {c = '+', u = '|', r = '-', d = '|'} -> '├'
      W {c = '+', u = '|', l = '-', d = '|'} -> '┤'
      W {c = '+', u = '|', l = '-', r = '-'} -> '┴'
      W {c = '-', d = '|'} -> '┬'
      W {c = '|', r = '-'} -> '├'
      W {c = '|', l = '-'} -> '┤'
      W {c = '-', u = '|'} -> '┴'
      W {c = '+', r = '-', d = '|'} -> '┌'
      W {c = '+', l = '-', d = '|'} -> '┐'
      W {c = '+', u = '|', l = '-'} -> '┘'
      W {c = '+', u = '|', r = '-'} -> '└'
      W {c = '.', r = '-', d = '|'} -> '╭'
      W {c = '.', l = '-', d = '|'} -> '╮'
      W {c = '.', u = '|', l = '-'} -> '╯'
      W {c = '.', u = '|', r = '-'} -> '╰'
      W {c = '\'', u = '|', l = '-'} -> '╯'
      W {c = '\'', u = '|', r = '-'} -> '╰'
      W {c = '^', d = '|'} -> '▲'
      W {c = 'v', u = '|'} -> '▼'
      W {c = '<', r = '-'} -> '◀'
      W {c = '>', l = '-'} -> '▶'
      W {c = c} -> c
```
