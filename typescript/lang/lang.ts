// Just a typescript implementation of 'Equational Reasoning about Formal Languages in Coalgebraic Style'
// Ref: https://www.cse.chalmers.se/~abela/jlamp17.pdf

abstract class Lang<T> {
  abstract accept(): boolean;
  abstract deriv(x: T): Lang<T>; // Brzozowski derivation

  test(word: ReadonlyArray<T>): boolean {
    return word.reduce<Lang<T>>((l, x) => l.deriv(x), this).accept();
  }
}

class Empty<T> extends Lang<T> {
  accept(): boolean {
    return false;
  }

  deriv(_x: T): Lang<T> {
    return this;
  }
}

class Epsilon<T> extends Lang<T> {
  accept(): boolean {
    return true;
  }

  deriv(_x: T): Lang<T> {
    return new Empty();
  }
}

class Single<T> extends Lang<T> {
  constructor(public x: T) {
    super();
  }

  accept(): boolean {
    return false;
  }

  deriv(x: T): Lang<T> {
    return x === this.x ? new Epsilon() : new Empty();
  }
}

class Union<T> extends Lang<T> {
  constructor(public lhs: Lang<T>, public rhs: Lang<T>) {
    super();
  }

  accept(): boolean {
    return this.lhs.accept() || this.rhs.accept();
  }

  deriv(x: T): Lang<T> {
    return this.lhs.deriv(x).union(this.rhs.deriv(x));
  }
}

class Concat<T> extends Lang<T> {
  constructor(public lhs: Lang<T>, public rhs: Lang<T>) {
    super();
  }

  accept(): boolean {
    return this.lhs.accept() && this.rhs.accept();
  }

  deriv(x: T): Lang<T> {
    return this.lhs.accept()
      ? this.lhs.deriv(x).concat(this.rhs).union(this.rhs.deriv(x))
      : this.lhs.deriv(x).concat(this.rhs);
  }
}

class Kleene<T> extends Lang<T> {
  constructor(public inner: Lang<T>) {
    super();
  }

  accept(): boolean {
    return true;
  }

  deriv(x: T): Lang<T> {
    return this.inner.deriv(x).concat(this);
  }
}

interface Lang<T> {
  union(other: Lang<T>): Lang<T>;
  concat(other: Lang<T>): Lang<T>;
  kleene(): Lang<T>;
}

Lang.prototype.union = function (this, other) {
  return new Union(this, other);
};

Lang.prototype.concat = function (this, other) {
  return new Concat(this, other);
};

Lang.prototype.kleene = function (this) {
  return new Kleene(this);
};

const t = new Single(true);
const f = new Single(false);
const binaryNumber = f.union(t.concat(t.union(f).kleene()));

console.group("test binaryNumber");
console.table({
  f: binaryNumber.test([false]),
  t: binaryNumber.test([true]),
  ftf: binaryNumber.test([false, true, false]),
  tft: binaryNumber.test([true, false, true]),
});
console.groupEnd();

const zero = new Single(0);
const nonZero = new Single(1)
  .union(new Single(2))
  .union(new Single(3))
  .union(new Single(4))
  .union(new Single(5))
  .union(new Single(6))
  .union(new Single(7))
  .union(new Single(8))
  .union(new Single(9));
const digit = zero.union(nonZero);
const number = zero.union(nonZero.concat(digit.kleene()));

console.group("test number");
console.table({
  "0": number.test([0]),
  "1": number.test([1]),
  "0123": number.test([0, 1, 2, 3]),
  "1234": number.test([1, 2, 3, 4]),
});
console.groupEnd();
