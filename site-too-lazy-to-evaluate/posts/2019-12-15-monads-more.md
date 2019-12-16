---
title: モナドを見分けるコツ
---

# 概要

広い範囲の多項式Functorについて、Monadになれるかどうかがわかった。

# 準備

ここでは、**多項式Functor**を、次の形をしたFunctor `F` のことと定義します。

```
F(x) ~ x^(a_0) + x^(a_1) + x^(a_2) + ... + x^(a_k)
```

ただし、`~`は`x`について自然な同型、`+`は直和型、`x^a`は`x`の`a`個の直積とします。
また、項の数`k`は0以上、すなわち`F(x)`は`Void`でもよいとします。また、`a_i`も0でもよいとします。
`x^0`はUnit型、ただ1つの値のみを持つ型です。

* Remark.
  * 有限個の値をとる型`e`に対して、`F(x) = Either e x, G(x) = (e,x), H(x) = e -> x`はすべて多項式Functorです。
  * 同じく`Const e`も多項式Functorです。
  * 多項式Functor`F, G`について、`(F :+: G)(x) = F x + G x`, `(F :*: G)(x) = F x * G x`は多項式Functorです。
  * 多項式Functorの合成は多項式Functorです。
  * 多項式Functor`F`は常に`Traversable`にできます。

よく知っているMonadのほとんどが多項式Functorです。ただし、ここでは`e`を有限な型とします。

* Identity Functor `newtype Id x = Id x`
* `Either e`
* `(,) e = Writer e`
* `(->) e = Reader e`
* `Maybe = Either ()`
* `Proxy = Const ()`

多項式Functorでないものももちろんあります。例えば`Cont r`がそうです。

また、すでにあるMonadのインスタンスから、新たなインスタンスを次々構成する方法が多数あります。
各種Monad Transformerなどはおなじみかと思いますが、それ以外にも次のようなものがあります：

* Monadの積。`Data.Functor.Product`という名前で`base`にもあるので、Monad則の証明は省きます。

  ```haskell
  newtype (*) f g a = f a :*: g a
  instance (Monad f, Monad g) => Monad (f * g)
  ```

* 単位の付加。モナド`M`に対して`T(x) = x + M(x)`もモナドにできます。

  ```haskell
  data T m x = TPure x | TLift (m x)
  
  lower :: (Monad m) => T m x -> m x
  lower (TPure x)  = return x
  lower (TLift mx) = mx
  
  instance (Monad m) => Monad (T m) where
    return = TPure
    TPure a  >>= k = k a
    TLift ma >>= k = TLift $ ma >>= lower . k
  ```

  単位則は簡単なので省き、結合則のみ示します。
  
  ```haskell
  -- 次の補題をまず示す。
  --   lower ma >>= lower . k  =  lower (ma >>= k)
  lower (TPure a) >>= lower . k
    = return a >>= lower . k
    = lower (k a)
    = lower (TPure a >>= k)
  lower (TLift ma) >>= lower . k
    = ma >>= lower . k
    = lower (TLift $ ma >>= lower . k)
    = lower (TLift ma >>= k)
 
  (TPure a >>= f) >>= g
    = f a >>= g
    = TPure a >>= (f >=> g)

  (TLift ma >>= f) >>= g
    = (TLift $ ma >>= lower . f) >>= g
    = TLift $ (ma >>= lower . f) >>= lower . g
      -- `Monad m`のMonad則によって変形できる
    = TLift $ ma >>= \a -> lower (f a) >>= lower . g
      -- 補題を使う
    = TLift $ ma >>= \a -> lower (f a >>= g)
    = TLift $ ma >>= lower . (\a -> f a >>= g)
    = TLift ma >>= \a -> (f a >>= g)
  ```

# 本論

ある多項式Functor `F`に対して、`F`のMonadのインスタンスが定義できるだろうか？という問題を考えます。
まず、これが常に可能であるわけではありません。例えば、`F ~ Const e`は`e`が2つ以上の異なる値を持つときにMonadになりません。加えて、先日の記事では以下の事実を示しました。

> `F ~ Maybe (e -> x)` は、`e`が2つ以上の異なる値を持つときにMonadにならない

一方で、非常に広い範囲の多項式Functorに対してMonadのインスタンスが定義できることもわかっています。
これらを組み合わせて、任意の多項式Functorに対してMonadのインスタンスが定義できるかどうかを判定する方法を示します。

* 主張0: ある多項式Functor`F`が `F(x) ~ c` と書けるならば、`|c| = 1`のとき、またそのときに限り`F`のMonadのインスタンスが存在する。
* 主張1: ある多項式Functor`F`が `F(x) ~ x * G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。
* 主張2: ある多項式Functor`F`が `F(x) ~ 1 + x + G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。
* 主張3: ある多項式Functor`F`が `F(x) ~ c + x^2 * G(x)`(`|c| >= 1, G(x) ~/~ 0`)と書けるならば、`F`のMonadのインスタンスが存在しない。
* 結論: `F(x) ~ c + x * b + x^2 * A(x)` に対してMonadのインスタンスが存在する ⇔ 以下のいずれかが成り立つ

  * `c = 1, b = 0, A(x) ~ 0`
  * `c = 0, b = 0, A(x) ~/~ 0`
  * `b >= 1`

主張0 ~ 主張3から結論が出ることは簡単に確かめられます。

## 主張0

> ある多項式Functor`F`が `F(x) ~ c` と書けるならば、`|c| = 1`のとき、またそのときに限り`F`のMonadのインスタンスが存在する。

### 証明

（以下、証明部分は常体で書きます）

(⇒)は[Proxy](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Proxy.html#t:Proxy)と同じようにMonadのインスタンスが定義できることからわかる。

(⇐)を示す。`pure :: x -> F x` はある定数関数 `const c0` である。このとき、`c0 :: F x ~ c` である。
任意の`c1 :: F x ~ c`について、`join (pure c1) = join (const c0 c1) = join c0`となるが、Monad則より`join . pure = id`なので`join (pure c1) = c1`でもある。したがって、任意の`c`型の値は`join c0`に等しい。これはすなわち、`|c| = 1`を意味する。

## 主張1

> ある多項式Functor`F`が `F(x) ~ x * G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。

例をあげると、

* `F(x) ~ x + x^3`
* `F(x) ~ x^2 + x^5 + x^6`

のように、「定数項」のないFunctorはMonadにできます。

### 証明

`F(x)`の項の数`k`および多項式の次数に関する帰納法を用いる。`k=1`のとき、すなわち`F(x) = x^a`のとき、`F`のMonadのインスタンスがあるのは明らか。

* `k>1`, かつ `G(x) ~ x * H(x)`と書けるならば、`G(x)`の次数は`F(x)`より小さいので、帰納法の仮定を用いれば `G(x)` はMonadにできる。`F(x) ~ x * G(x) ~ (Id * G)(x)`かつIdもGもMonadなので、Monadの積によって`F(x)`もMonadのインスタンスを持てる。
* `k>1`, かつ`G(x) ~ x * H(x)`と書けないならば、`G(x) ~ 1 + H(x)`と書ける。このとき、
  
  ```
  F(x) ~ x * (1 + H(x)) ~ x + x * H(x) ~ x + (Id * H)(x)
  ```

  かつ、`(Id * H)(x)`の項の数は`F(x)`より一つ少ないので、帰納法の仮定を用いれば`(Id * H)(x)`はMonadにできる。
  よって、先程述べた"単位の付加"の構成により、`F(x) ~ x + (Id * H)(x)`はMonadにできる。

## 主張2

> ある多項式Functor`F`が `F(x) ~ 1 + x + G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。

例:

* `F(x) ~ c + b * x`, 言い換えれば `F x = Either C (B, x)`であるとき、`c >= 1`, `b >= 1`ならばMonadのインスタンスが存在します。`F x ~ WriterT B (Either C) x`、および任意の空でない型`B`に対して`Monoid B`が定義できることを考えれば、これは納得がいきます。
* `F(x) ~ 1 + x + x^2 + x^3`, 長さが 0 〜 3 のリストにはMonadのインスタンスが存在します。

### 証明

どの多項式FunctorもTraversableにできるのであった。`G(x)`も`Traversable`であると仮定してよい。
次のように `F x ~ U g x = 1 + x + g x` とそのMonadのインスタンスを定義する。

```haskell
data U g x = Nothing' | Just' x | Wrap (g x)

toMaybe :: U g x -> Maybe x
toMaybe (Just' x) = Just x
toMaybe _         = Nothing

instance (Traversable g) => Monad (U g x) where
  return = Just'
  Nothing' >>= _ = Nothing'
  Just' a  >>= k = k a
  Wrap ga  >>= k = maybe Nothing' Wrap $ traverse (toMaybe . k) ga
```

これがMonad則を満たすことを確認する。

```haskell
[toMaybeはMonad morphism]
toMaybe . return = toMaybe . Just' = Just = return

toMaybe (ma >>= k)
 = case ma of
     Nothing' -> toMaybe (Nothing' >>= k)
     Just' a  -> toMaybe (Just' a >>= k)
     Wrap ga  -> toMaybe (Wrap ga >>= k)
 = case ma of
     Nothing' -> toMaybe Nothing'
     Just' a  -> toMaybe (k a)
     Wrap ga  -> toMaybe (maybe Nothing' Wrap $ ...)
 = case ma of
     Nothing' -> Nothing
     Just' a  -> toMaybe (k a)
     Wrap _   -> Nothing
 = case toMaybe ma of
     Nothing -> Nothing
     Just a  -> toMaybe (k a)
 = toMaybe ma >>= toMaybe . k
(系) toMaybe (f >=> g) = toMaybe f >=> toMaybe g

[左単位] return a >>= k = k a
return a >>= k
 = Just' a >>= k
 = k a

[右単位] ma >>= return = ma
Nothing' >>= return = Nothing'
Just' a  >>= return = Just' a
Wrap ga  >>= return
 = maybe Nothing' Wrap $ traverse (toMaybe . return) ga
 = maybe Nothing' Wrap $ traverse Just ga
    -- traverse則, traverse pure = pure および pure @Maybe = Just
 = maybe Nothing' Wrap $ Just ga
 = Wrap ga

[結合] (ma >>= f) >>= g = ma >>= (f >=> g)
(Nothing' >>= f) >>= g   =   Nothing'    =   Nothing' >>= (f >=> g)
(Just' a  >>= f) >>= g   =   f a >>= g   =   Just' a  >>= (f >=> g)

(Wrap ga >>= f) >>= g
 = (maybe Nothing' Wrap $ traverse (toMaybe . f) ga) >>= g
 = case traverse (toMaybe . f) ga of
     Nothing -> Nothing' >>= g
     Just gb -> Wrap gb >>= g
 = case traverse (toMaybe . f) ga of
     Nothing -> Nothing'
     Just gb -> maybe Nothing' Wrap $ traverse (toMaybe . g) gb
 = maybe Nothing' Wrap $ case traverse (toMaybe . f) ga of
     Nothing -> Nothing
     Just gb -> traverse (toMaybe . g) gb
 = maybe Nothing' Wrap $ traverse (toMaybe . f) ga >>= traverse (toMaybe . g)
Wrap ga >>= (f >=> g)
 = maybe Nothing' Wrap $ traverse (toMaybe . (f >=> g)) ga
    -- toMaybe が Monad morphismであることを用いる
 = maybe Nothing' Wrap $ traverse (toMaybe . f >=> toMaybe . g) ga
    -- Maybeでtraverse補題(後述)を用いる
 = maybe Nothing' Wrap $ (traverse (toMaybe . f) >=> traverse (toMaybe . g)) ga
 = maybe Nothing' Wrap $ traverse (toMaybe . f) ga >>= traverse (toMaybe . g)

[Maybeでtraverse補題]
任意の
    f :: a -> Maybe b
    g :: b -> Maybe c
に対して、
    traverse (f >=> g) = traverse f >=> traverse g
(証明)
    join' :: forall x. Compose Maybe Maybe x -> Maybe x
    join' (Compose mmx) = join mmx
を用いると、
    f >=> g = join' . Compose . fmap g . f
と変形できる。
また、証明は略するが join' はApplicative transformation である。
    join' . pure = pure
    join' (x <*> y) = join' x <*> join' y
よって、
    traverse (f >=> g)
      = traverse (join' . Compose . fmap g . f)
        -- Traversable則 naturality
      = join' . traverse (Compose . fmap g . f)
        -- Traversable則 composition
      = join' . Compose . fmap (traverse g) . traverse f
        -- join' の定義
      = join . fmap (traverse g) . traverse f
        -- (>=>) の定義
      = traverse f >=> traverse g
(証明終)
(注:一般のMonadに対してjoin'はApplicative transformationにならないので、
Maybeを任意のMonadに置き換えることはできない。)
```

## 主張3

**2019.12.16 追記** ― 証明を読みやすく、あと有限性に依存しないようにできたので[修正版を投稿しました](./2019-12-16-fixed-proof-for-monads-more.html)

> ある多項式Functor`F`が `F(x) ~ c + x^2 * G(x)`(`|c| >= 1, G(x) ~/~ 0`)と書けるならば、`F`のMonadのインスタンスは存在しない。

例:

* `F(x) ~ 1 + x^2`
* `F(x) ~ 3 + x^2 + x^4`

### 証明

まず、どんな多項式Functorに対しても、`forall x. x -> F x`という型を持つ関数があれば、それは`F(x)`の特定の項
`F(x) ~ ... + x^n + ...`に対応するコンストラクタに、`n`個の`x`のコピーを渡した値を返す。このコンストラクタは、当然、`x`に依存せずに決まる。

いま問題としている`F(x) ~ c + x^2 * G(x)`において、Monadの定義における`return :: forall x. x -> F x`に対応する項が`x^n`であるとしたら、`n == 0`であるか、または`n >= 2`である。

仮に`n == 0`であったとする。これはすなわち`return`は定数関数であり、`return x`の値は`x`に依存しないことを意味している。しかし、Monad則より`join (return fx) = fx`でなければならず、また空でない型`X`において`fx :: F X`は2つ以上の異なる値を持つので、`return`は定数関数であってはならない。したがって、`n >= 2`でなければならない。

`return`の返り値に対応する項`x^n`を明示して、`F(x)`が以下のように定義されているとする。

```haskell
type N = ...
type C = ...
type G x = ...

data F x = U (N -> x) | L C | R x x (G x)

return :: forall x. x -> F x
return x = U (const x)
```

また、前提条件として与えられている、`C`に1つ以上の値があることが、次のように表されているとする。

```haskell
-- |C| >= 1
c0 :: C
zero :: forall x. F x
zero = L c0
```

簡単にわかることとして、`join zero = zero`がある。

```haskell
join (L c0)
 -- fmap f (L c) = L c
 = join (fmap return $ L c0)
 = join . fmap return $ L c0
 -- join . fmap return = id
 = L c0
```

Monad則から、`join :: F (F x) -> F x`の満たすべき等式として次のものが得られる。

```haskell
-- ∀a :: N -> N -> x
join $ U (\i -> U (\j -> a i j)) = U $ \i -> a i i
```

以降、この等式は`joinUU`という名前で呼ぶ。また、これは次のように証明できる。

```haskell
coord :: F (F (N, N))
coord = U $ \i -> U $ \j -> (i,j)

fmap fst (join coord)
 = join (fmap (fmap fst) coord)
 = join (U $ \i -> U $ \j -> i)
 = join (U $ \i -> return i)
 = join (fmap return (U $ \i -> i))
   -- Monad則(join . fmap return = id)
 = U $ \i -> i

fmap snd (join coord)
 = join (fmap (fmap snd) coord)
 = join (U $ \i -> U $ \j -> j)
 = join (return $ U $ \j -> j)
   -- Monad則(join . return = id)
 = U $ \j -> j

join coord = U $ \i -> (i,i)

join $ U (\i -> U (\j -> a i j))
 = join $ fmap (fmap (uncurry a)) coord
 = fmap (uncurry a) $ join coord
 = fmap (uncurry a) $ U $ \i -> (i,i)
 = U $ \i -> a i i
```

ここで、次の関数を考える。

```haskell
at :: forall x. N -> x -> F x
at i x = join $ U (\j -> if i == j then return x else zero)
```

いま、ある`i :: N`において`at i x`が`x`に依存しないと仮定する。
このとき、次の`sweep f`は`f i`の値に依存しないはずである。

```haskell
sweep :: forall x. (N -> x) -> F (F x)
sweep f = U $ \j -> at j (f j)
```

一方、`join $ sweep f`を`join`の結合則を用いて計算すると、以下のようになる。

```haskell
join $ sweep f
 = join $ U (\j -> at j (f j))
 = join $ U (\j -> join $ U (\k -> if j == k then return (f j) else zero))
 = join . fmap join $ U (\j -> U (\k -> if j == k then return (f j) else zero))
 -- 結合則
 = join . join $ U (\j -> U (\k -> if j == k then return (f j) else zero))
 -- joinUU
 = join $ U (\j -> if j == j then return (f j) else zero)
 = join $ U (\j -> return (f j))
 = join . fmap return $ U (\j -> f j)
 -- 単位則
 = U f
```

これは明らかに`f`の任意の点`i :: N`での値に依存する。これは矛盾である。

* **事実1**: 任意の`i`に対して`at i x`は`x`に依存する。

次に、`at i /= return`を示す。

```haskell
U f >>= return
 = U f
U f >>= at i
 = join $ U (\j -> at i (f j))
 = join $ U (\j -> join $ U (\k -> if i == k then return (f j) else zero))
 = join . fmap join $ U (\j -> U (\k -> if i == k then return (f j) else zero))
 = join . join $ U (\j -> U (\k -> if i == k then return (f j) else zero))
 = join $ U (\j -> if i == j then return (f j) else zero)
 = join $ U (\j -> if i == j then return (f i) else zero)
 = at i (f i)
```

いま、`N`には2つ以上の異なる値があるので、`i' /= i`なる`i' :: N`が存在して、`U f`は`f i`にも`f i'`にも依存する。
しかし、`at i (f i)`は`f i`にしか依存しないので、`at i = return` ではありえない。

* **事実2**: 任意の`i`に対して`at i /= return`

加えて、

```haskell
hole :: (N -> x) -> N -> (x -> F x) -> F x
hole f i u = join $ \j -> if i == j then u (f j) else return (f j)

hole f i (at k)
 = join $ U $ \j -> if i == j then at k (f j) else return (f j)
 = join $ U $ \j -> if i == j
     then join $ U (\l -> if k == l then return (f j) else zero)
     else join . return . return $ f j
 = join . fmap join $ U $ \j -> if i == j
     then U (\l -> if k == l then return (f j) else zero)
     else U (\_ -> return (f j))
 -- 結合則 + joinUU
 = join $ U $ \j ->
     if i == j
       then if k == j then return (f j) else zero
       else return (f j)

-- i == k のとき
hole f i (at k) | i == k
 = join $ U $ \j -> if (i == j) then return (f j) else return (f j)
 = join $ U $ \j -> return (f j)
 = U f

-- i /= k のとき
hole f i (at k) | i /= k
 = join $ U $ \j ->
     if i == j then zero else return (f j)
```

より、`hole f i (at k)`が`f i`に依存するかどうかは、`i == k`かどうかによって決まる。したがって、`i /= k`のとき、`at i /= at k`である。

* **事実3**: 任意の`i, k :: N`に対して、`i /= k`ならば`at i /= at k` 

いま、`at i x`は`x`に依存するのであった。`return`のときと同様の議論によって、`at i x`が返すコンストラクタは2つ以上の`x`の値に依存することができるので、関数`con :: N -> x -> x -> F x`が存在して、`con i x y`は`x`と`y`の両方に依存し、
`con i x x = at i x`となるようにできる。

`con i`に関する等式をいくつか示す。

```haskell
join $ U (\j -> if i == j then zero else at i x)
 = join $ U (\j -> if i == j then join (return zero) else join $ U (\k -> if i == k then return x else zero))
 = join . fmap join $ U $ \j ->
     if i == j then return zero else U (\k -> if i == k then return x else zero)
 = join . join $ U $ \j -> U $ \k ->
     if i == j then zero else (if i == k then return x else zero)
 = join $ U $ \j ->
     if i == j then zero else (if i == j then return x else zero)
 = join $ U $ \j -> if i == j then zero else zero
 = join $ return zero
 = zero

-- Because `join` can't discriminate between `at i x = con i x x` and `con i x y`:
join $ U (\j -> if i == j then zero else con i x y)
 = zero

join $ at i (con i x y)
 = join . join $ U (\j -> if i == j then return (con i x y) else zero)
 = join $ U (\j -> if i == j then join (return (con i x y)) else join zero)
 = join $ U (\j -> if i == j then con i x y else zero)
  -- Use above equation in reversed direction
 = join $ U $ \j ->
     if i == j
       then con i x y
       else join $ U (\k -> if i == k then zero else con i x y)
 = join $ U $ \j ->
     if i == j
       then join $ return (con i x y)
       else join $ U (\k -> if i == k then zero else con i x y)
 = join . fmap join $ U $ \j -> U $ \k ->
     if i == j
       then con i x y
       else (if i == k then zero else con i x y)
 = join $ U $ \j ->
     if i == j
       then con i x y
       else (if i == j then zero else con i x y)
 = join $ U $ \j -> con i x y
 = join . return $ con i x y
 = con i x y
```

いま、次の関数`extra`を考える。

```haskell
extra :: forall x. N -> x -> x -> (N -> x) -> F x
extra i x y f = join $ U (\j -> if i == j then con i x y else return (f j))
```

次の計算によって、2つのことがわかる。

```haskell
extra i (f i) (f i) f
 = join $ U (\j -> if i == j then con i (f i) (f i) else return (f j))
 = join $ U (\j -> if i == j then at i (f i) else return (f j))
 = hole f i (at i)
 = U f
```

まず、`extra`は`x`に関して自然なので、任意の`x, y, f`に関して`extra i x y f = U _`とならなければならない。
また、`extra i x y f`は任意の`j /= i`における`f j`と、`x`, `y`のいずれか片方に依存する。

さらに、

```haskell
join $ at i (extra i x y f)
 = join . join $ U $ \j -> if i == j then extra i x y f else zero
 = join . join $ U $ \j ->
     if i == j
       then join $ U (\k -> if i == k then con i x y else return (f k))
       else join (return zero)
 = join . join . fmap join $ U $ \j ->
     if i == j
       then U (\k -> if i == k then con i x y else return (f k))
       else return zero
 = join . join . join $ U $ \j -> U $ \k ->
     if i == j
       then if i == k then con i x y else return (f k)
       else zero
 = join . join $ U $ \j ->
     if i == j
       then if i == j then con i x y else return (f j)
       else zero
 = join . join $ U $ \j -> if i == j then con i x y else zero
 = join $ at i (con i x y)
 = con i x y
```

である。したがって、`extra i x y f`は`x`と`y`の両方に依存する。

さて、`extra i x y f = U g`と書くことができ、`g :: N -> x`なのであった。`g`は任意の`j /= i`における`f j`、`x`、そして`y`のいずれにも依存する。しかし、`N`が有限であればこれは`N+1`個の独立な変数なので、これは不可能である。

* **事実4**: `N`は無限個の異なる値をとる。

さらに、`at i`は各`i`について異なる必要があるので、

* **事実5**: `F(x)`は無限個の項の和である。

いま、多項式Functorは、有限な型`a_i`について`x^(a_i)`の有限個の直和型として定義したのであった。よって、ここで定義した`F(x)`は`Monad`になることはない。
