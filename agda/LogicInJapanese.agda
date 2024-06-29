module LogicInJapanese where

open import Agda.Builtin.Equality
  using ( _≡_ )
  renaming ( refl to 定義より等価 )
open import Agda.Builtin.Nat
  using ( zero )
  renaming ( Nat to 自然数; suc to 1+_ )

--------------------------------------------------------------------------------

infix 0 _である
infix 1 任意-syntax 存在-syntax
infixr 2 _ならば_
infixr 3 _または_
infixr 4 _かつ_
infix 5 _ではない

infix 3 _が矛盾するから _であるから
infixr 4 _と_ _で_

命題 : Set₁
命題 = Set

private
  variable
    P Q R : 命題
    m n : 自然数

data 真 : 命題 where
  自明 : 真

data 偽 : 命題 where

_ではない : 命題 → 命題
P ではない = P → 偽

_である : 命題 → 命題
P である = P

data _かつ_ (P Q : 命題) : 命題 where
  _と_ : P → Q → P かつ Q

data _または_ (P Q : 命題) : 命題 where
  前者 : P → P または Q
  後者 : Q → P または Q

_ならば_ : 命題 → 命題 → 命題
P ならば Q = P → Q

任意-syntax : (P : 命題) (Q : P → 命題) → 命題
任意-syntax P Q = (x : P) → Q x
syntax 任意-syntax P (λ x → Q) = 任意の x ∈ P に対して Q

data 存在 (P : 命題) (Q : P → 命題) : 命題 where
  _で_ : (x : P) → Q x → 存在 P Q

存在-syntax : (P : 命題) (Q : P → 命題) → 命題
存在-syntax P Q = 存在 P Q
syntax 存在-syntax P (λ x → Q) = ある x ∈ P が存在して Q

_であるから : P → P
Pの証明 であるから = Pの証明

_が矛盾するから : P かつ P ではない ならば 偽 である
(Pである と Pではない) が矛盾するから = Pではない Pである

--------------------------------------------------------------------------------

ド・モルガン : (P ではない または Q ではない) ならば (P かつ Q) ではない
ド・モルガン (前者 Pではない) (Pである と Qである) = Pである と Pではない が矛盾するから
ド・モルガン (後者 Qではない) (Pである と Qである) = Qである と Qではない が矛盾するから

mutual
  data _は偶数 : 自然数 → 命題 where
    0は偶数 : 0 は偶数
    一つ前の_ : n は奇数 → (1+ n) は偶数

  data _は奇数 : 自然数 → 命題 where
    1は奇数 : 1 は奇数
    一つ前の_ : n は偶数 → (1+ n) は奇数

言明1 : 任意の n ∈ 自然数 に対して n は偶数 または n は奇数 である
言明1 0 = 前者 0は偶数 であるから
言明1 (1+ n) with 言明1 n
... | 前者 nは偶数 = 後者 (一つ前の nは偶数) であるから
... | 後者 nは奇数 = 前者 (一つ前の nは奇数) であるから

言明2 : ある x ∈ 自然数 が存在して x は偶数 である
言明2 = 0 で 0は偶数 であるから
