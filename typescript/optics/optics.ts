// Ref: https://qiita.com/dico_leque/items/cc0a0162f17cea8f8ae0

type Brand<K, T> = K & { __brand: T };

type Optic<K, S, T, A, B> = Brand<
  <R>(f: (a: A, k: (b: B) => R) => R) => (s: S, k: (t: T) => R) => R,
  K
>;

interface Setter {
  setter: void;
}

interface Getter {
  getter: void;
}

interface Lens extends Setter, Getter {
  lens: void;
}

interface Prism extends Setter {
  prism: void;
}

interface Iso extends Lens, Prism {
  iso: void;
}

function id<S, A>(): Optic<Iso, S, A, S, A> {
  return ((f) => f) as Optic<Iso, S, A, S, A>;
}

function comp<K, S, T, U, V, A, B>(
  o1: Optic<K, S, T, U, V>,
  o2: Optic<K, U, V, A, B>
): Optic<K, S, T, A, B> {
  return ((f) => o1(o2(f))) as Optic<K, S, T, A, B>;
}

function lens<S, T, A, B>(
  get: (s: S) => A,
  set: (s: S, b: B) => T
): Optic<Lens, S, T, A, B> {
  return ((f) => (s, k) => f(get(s), (b) => k(set(s, b)))) as Optic<
    Lens,
    S,
    T,
    A,
    B
  >;
}

function over<S, T, A, B>(
  l: Optic<Setter, S, T, A, B>,
  f: (a: A) => B,
  s: S
): T {
  return l<T>((a, k) => k(f(a)))(s, (t) => t);
}

function set<S, T, A, B>(l: Optic<Setter, S, T, A, B>, b: B, s: S): T {
  return over(l, (_) => b, s);
}

function get<S, T, A, B>(l: Optic<Getter, S, T, A, B>, s: S): A {
  return l<A>((a, _) => a)(s, (_) => {
    throw new Error("impossible");
  });
}

const _1 = <A, B, C>() =>
  lens<[A, B], [C, B], A, C>(
    ([a, _]) => a,
    ([_, b], c) => [c, b]
  );

const _2 = <A, B, C>() =>
  lens<[A, B], [A, C], B, C>(
    ([_, b]) => b,
    ([a, _], c) => [a, c]
  );

function prism<S, T, A, B>(
  build: (b: B) => T,
  match: (s: S) => [true, A] | [false, T]
): Optic<Prism, S, T, A, B> {
  return ((f) => (s, k) => {
    const res = match(s);
    return res[0] ? f(res[1], (b) => k(build(b))) : k(res[1]);
  }) as Optic<Prism, S, T, A, B>;
}

const _Some = <A, B>() =>
  prism<A | null, B | null, A, B>(
    (b) => b,
    (a) => (a ? [true, a] : [false, null])
  );

const t: [[number, number], number] = [[1, 2], 3];
console.log(t);
console.log(
  get(comp(_1<[number, number], number, [number, number]>(), _1()), t)
);
console.log(
  set(comp(_1<[number, number], number, [number, number]>(), _1()), 10, t)
);

const foo = () =>
  comp<
    Setter,
    [number, number] | null,
    [number, number] | null,
    [number, number],
    [number, number],
    number,
    number
  >(_Some(), _1());

console.log(over(foo(), (x) => x + 10, [1, 2]));
console.log(over(foo(), (x) => x + 10, null));
