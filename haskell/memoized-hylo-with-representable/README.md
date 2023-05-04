# Memoized Hylomorphism with Representable Functors

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hyloMemo :: (Representable t, Functor f) => (f b -> b) -> (Rep t -> f (Rep t)) -> Rep t -> b
```

```plain
benchmarking fib/10
time                 2.474 μs   (2.461 μs .. 2.487 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 2.465 μs   (2.458 μs .. 2.473 μs)
std dev              26.68 ns   (23.22 ns .. 31.44 ns)

benchmarking fib/20
time                 298.4 μs   (286.3 μs .. 313.8 μs)
                     0.992 R²   (0.985 R² .. 1.000 R²)
mean                 286.9 μs   (284.0 μs .. 293.9 μs)
std dev              14.28 μs   (5.515 μs .. 25.52 μs)
variance introduced by outliers: 47% (moderately inflated)

benchmarking fib/30
time                 34.64 ms   (34.19 ms .. 35.03 ms)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 34.96 ms   (34.78 ms .. 35.38 ms)
std dev              561.3 μs   (281.0 μs .. 988.7 μs)

benchmarking fib/35
time                 383.9 ms   (381.8 ms .. 388.6 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 384.1 ms   (383.3 ms .. 384.9 ms)
std dev              1.010 ms   (473.0 μs .. 1.352 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking fibMemo/10
time                 91.79 ns   (91.22 ns .. 92.68 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 91.49 ns   (91.30 ns .. 92.14 ns)
std dev              1.023 ns   (366.5 ps .. 2.198 ns)
variance introduced by outliers: 11% (moderately inflated)

benchmarking fibMemo/20
time                 160.1 ns   (158.6 ns .. 161.8 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 159.9 ns   (158.7 ns .. 161.9 ns)
std dev              4.972 ns   (2.849 ns .. 8.271 ns)
variance introduced by outliers: 47% (moderately inflated)

benchmarking fibMemo/30
time                 223.4 ns   (222.9 ns .. 224.0 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 223.5 ns   (223.1 ns .. 224.5 ns)
std dev              2.317 ns   (1.480 ns .. 3.661 ns)

benchmarking fibMemo/35
time                 257.4 ns   (257.1 ns .. 257.8 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 257.5 ns   (257.1 ns .. 258.8 ns)
std dev              2.217 ns   (558.4 ps .. 4.582 ns)

benchmarking fibMemo/100
time                 696.0 ns   (694.1 ns .. 698.6 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 698.0 ns   (694.6 ns .. 702.2 ns)
std dev              12.50 ns   (9.380 ns .. 16.40 ns)
variance introduced by outliers: 20% (moderately inflated)

benchmarking fibMemo/1000
time                 6.825 μs   (6.742 μs .. 6.931 μs)
                     0.998 R²   (0.996 R² .. 0.999 R²)
mean                 6.908 μs   (6.811 μs .. 7.065 μs)
std dev              392.2 ns   (256.2 ns .. 538.4 ns)
variance introduced by outliers: 67% (severely inflated)

benchmarking fibMemo/10000
time                 77.91 μs   (77.73 μs .. 78.14 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 78.08 μs   (77.94 μs .. 78.31 μs)
std dev              578.7 ns   (456.0 ns .. 734.2 ns)

benchmarking fibMemo/50000
time                 823.4 μs   (723.5 μs .. 973.9 μs)
                     0.892 R²   (0.823 R² .. 0.984 R²)
mean                 756.7 μs   (721.2 μs .. 831.7 μs)
std dev              159.2 μs   (91.71 μs .. 302.7 μs)
variance introduced by outliers: 93% (severely inflated)

benchmarking fibMemoFin/10
time                 30.39 ns   (30.26 ns .. 30.51 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 30.32 ns   (30.25 ns .. 30.44 ns)
std dev              318.4 ps   (211.9 ps .. 458.9 ps)
variance introduced by outliers: 10% (moderately inflated)

benchmarking fibMemoFin/20
time                 30.27 ns   (30.21 ns .. 30.35 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 30.35 ns   (30.28 ns .. 30.47 ns)
std dev              303.0 ps   (194.6 ps .. 483.2 ps)

benchmarking fibMemoFin/30
time                 28.29 ns   (28.27 ns .. 28.31 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 28.33 ns   (28.28 ns .. 28.51 ns)
std dev              235.5 ps   (58.13 ps .. 520.2 ps)

benchmarking fibMemoFin/35
time                 29.07 ns   (28.87 ns .. 29.27 ns)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 29.05 ns   (28.82 ns .. 29.48 ns)
std dev              1.015 ns   (644.7 ps .. 1.658 ns)
variance introduced by outliers: 56% (severely inflated)

benchmarking fibMemoFin/100
time                 27.44 ns   (27.29 ns .. 27.57 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 27.38 ns   (27.29 ns .. 27.51 ns)
std dev              354.9 ps   (287.0 ps .. 440.8 ps)
variance introduced by outliers: 15% (moderately inflated)

benchmarking fibMemoFin/1000
time                 23.77 ns   (23.73 ns .. 23.82 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 23.79 ns   (23.75 ns .. 23.90 ns)
std dev              227.0 ps   (88.86 ps .. 436.2 ps)

benchmarking fibMemoFin/10000
time                 22.84 ns   (22.77 ns .. 22.91 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 22.88 ns   (22.84 ns .. 22.94 ns)
std dev              167.7 ps   (142.6 ps .. 206.5 ps)

benchmarking fibMemoFin/50000
time                 26.66 ns   (26.62 ns .. 26.73 ns)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 27.36 ns   (27.02 ns .. 27.91 ns)
std dev              1.417 ns   (990.4 ps .. 1.893 ns)
variance introduced by outliers: 74% (severely inflated)
```
