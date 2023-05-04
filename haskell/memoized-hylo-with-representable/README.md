# Memoized Hylomorphism with Representable Functors

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hyloMemo :: (Representable t, Functor f) => (f b -> b) -> (Rep t -> f (Rep t)) -> Rep t -> b
```

```plain
benchmarking fib/10
time                 3.906 μs   (3.892 μs .. 3.922 μs)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 3.964 μs   (3.917 μs .. 4.062 μs)
std dev              215.5 ns   (129.7 ns .. 364.7 ns)
variance introduced by outliers: 67% (severely inflated)

benchmarking fib/20
time                 363.9 μs   (362.3 μs .. 366.9 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 365.0 μs   (364.0 μs .. 366.8 μs)
std dev              4.459 μs   (2.916 μs .. 7.423 μs)

benchmarking fib/30
time                 44.50 ms   (44.34 ms .. 44.63 ms)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 44.58 ms   (44.51 ms .. 44.81 ms)
std dev              217.9 μs   (73.50 μs .. 386.4 μs)

benchmarking fib/35
time                 510.6 ms   (491.5 ms .. 540.2 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 499.8 ms   (495.4 ms .. 505.3 ms)
std dev              6.048 ms   (1.734 ms .. 8.198 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking fibMemo/10
time                 103.4 ns   (103.2 ns .. 103.6 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 103.4 ns   (103.2 ns .. 103.7 ns)
std dev              753.2 ps   (657.5 ps .. 906.4 ps)

benchmarking fibMemo/20
time                 176.6 ns   (176.1 ns .. 177.3 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 176.9 ns   (176.5 ns .. 177.5 ns)
std dev              1.707 ns   (1.346 ns .. 2.605 ns)

benchmarking fibMemo/30
time                 248.3 ns   (247.3 ns .. 249.3 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 247.3 ns   (246.9 ns .. 247.9 ns)
std dev              1.622 ns   (1.254 ns .. 2.037 ns)

benchmarking fibMemo/35
time                 288.0 ns   (286.6 ns .. 290.3 ns)
                     0.999 R²   (0.997 R² .. 1.000 R²)
mean                 290.6 ns   (288.2 ns .. 297.5 ns)
std dev              12.21 ns   (5.078 ns .. 25.57 ns)
variance introduced by outliers: 61% (severely inflated)

benchmarking fibMemo/100
time                 761.7 ns   (758.4 ns .. 765.1 ns)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 766.9 ns   (764.1 ns .. 769.9 ns)
std dev              9.566 ns   (7.960 ns .. 11.90 ns)
variance introduced by outliers: 11% (moderately inflated)

benchmarking fibMemo/1000
time                 7.335 μs   (7.311 μs .. 7.356 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 7.332 μs   (7.314 μs .. 7.363 μs)
std dev              76.62 ns   (54.73 ns .. 126.8 ns)

benchmarking fibMemo/10000
time                 84.24 μs   (83.98 μs .. 84.53 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 84.47 μs   (84.29 μs .. 84.67 μs)
std dev              661.0 ns   (581.3 ns .. 780.4 ns)

benchmarking fibMemo/50000
time                 692.0 μs   (676.8 μs .. 715.6 μs)
                     0.986 R²   (0.959 R² .. 0.999 R²)
mean                 694.0 μs   (683.4 μs .. 732.4 μs)
std dev              60.37 μs   (16.71 μs .. 122.7 μs)
variance introduced by outliers: 69% (severely inflated)
```
