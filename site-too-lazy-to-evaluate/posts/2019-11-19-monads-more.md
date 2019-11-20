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

* 主張1: ある多項式Functor`F`が `F(x) ~ x * G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。
* 主張2: ある多項式Functor`F`が `F(x) ~ 1 + x + G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。
* 主張3: ある多項式Functor`F`が `F(x) ~ c + x^2 * G(x)`(`|c| >= 1`)と書けるならば、`F`のMonadのインスタンスが存在しない。
* 結論: `F(x) ~ c + b * x + A(x) * x^2` に対してMonadのインスタンスが存在する ⇔ 以下のいずれかが成り立つ

  * `c = 1, b = 0, A(x) ~ 0`
  * `c = 0, b = 0, A(x) ~/~ 0`
  * `b >= 1`

## 主張1

> ある多項式Functor`F`が `F(x) ~ x * G(x)` と書けるならば、`F`のMonadのインスタンスが存在する。

例をあげると、

* `F(x) ~ x + x^3`
* `F(x) ~ x^2 + x^5 + x^6`

のように、「定数項」のないFunctorはMonadにできます。

### 証明

（証明部分は常体で書きます）

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

（証明部分は常体で書きます）

どの多項式FunctorもTraversableにできるのであった。`G(x)`も`Traversable`であると仮定してよい。
次のように `F x ~ U g x ~ 1 + x + g x` とそのMonadのインスタンスを定義する。

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

> ある多項式Functor`F`が `F(x) ~ c + x^2 * G(x)`(`|c| >= 1`)と書けるならば、`F`のMonadのインスタンスは存在しない。

例:

* `F(x) ~ 1 + x^2`
* `F(x) ~ 3 + x^2 + x^4`

### 証明

TODO: まだ

