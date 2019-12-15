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

## 主張0

> ある多項式Functor`F`が `F(x) ~ c` と書けるならば、`|c| = 1`のとき、またそのときに限り`F`のMonadのインスタンスが存在する。

### 証明

（証明部分は常体で書きます）

(⇒)は(Proxy)[http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Proxy.html#t:Proxy]と同じようにMonadのインスタンスが定義できることからわかる。

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

また、前提条件として与えられている、`C`に1つ以上の値があること及び`N`に2つ以上の異なる値があるという事実が、
次のように表されているとする。

```haskell
-- |C| >= 1
c0 :: C

-- |N| >= 2
-- p is surjective (f . p = g . p -> f = g)
p :: N -> Bool
```

Monad則から、`join :: F (F x) -> F x`の満たすべき等式として次のものが得られる。

```haskell
-- ∀a :: N -> N -> x
join $ U (\i -> U (\j -> a i j)) = U $ \i -> a i i
```

これは次のように証明できる。

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

これらの条件を用いて、`join`が結合則を満たすことがないことを示す。

まず、次の補助関数を定義する。

```haskell
(?) :: x -> x -> F x
(?) x y = U $ \i -> if p i then x else y

infix 5 ?

zero :: F x
zero = L c0

ifP :: x -> F (F x)
ifP x = return x ? zero

unlessP :: x -> F (F x)
unlessP x = zero ? return x
```

これらを用いて、`join`の結合則を満たさないような反例をあげることができる。その準備として、次の等式を確認する。

```
x ? x
 = U $ \i -> if p i then x else x
 = U $ \i -> x
 = return x

join $ (x ? y) ? (z ? w)
 = join $ U $ \i ->
     if p i then U $ \j -> if p j then x else y
            else U $ \j -> if p j then z else w
 = join $ U $ \i -> U $ \j -> 
     if p i then (if p j then x else y)
            else (if p j then z else w)
 = U $ \i ->
     if p i then (if p i then x else y)
            else (if p i then z else w)
 = U $ \i -> if p i then x else w
 = x ? w
```

次の`bad1`において結合則を確認する。

```haskell
bad1 :: x -> x -> F (F (F x))
bad1 x y = ifP x ? unlessP y

(join . join) (bad1 x y)
 = join . join $ ifP x ? unlessP y
 = join . join $ (return x ? zero) ? (zero ? return y)
 = join $ return x ? return y
 = join $ (x ? x) ? (y ? y)
 = x ? y
   -- x, yの両方に依存する

(join . fmap join) (bad1 x y)
 = join . fmap join $ ifP x ? unlessP y
 = join $ join (ifP x) ? join (unlessP y)
```

前者が`x`に依存する値を返すので、後者もそうでなければならない。そのためには、`join (ifP x)`は`x`に依存しなければならない。同様に、`join (unlessP y)`も`y`に依存しなければならない。

```haskell
fboolT, fboolF :: x -> x -> F x
fboolT x y = join $ (x ? y) ? zero
fboolF x y = join $ zero    ? (x ? y)

join . join $ ((x ? y) ? (z ? w)) ? (zero ? zero)
 = join $ (x ? y) ? zero
 = fboolT x y
join . fmap join $ ((x ? y) ? (z ? w)) ? (zero ? zero)
 = join $ (join $ (x ? y) ? (z ? w)) (join $ zero ? zero)
 = join $ (x ? w) ? zero
 = fboolT x w
```

したがって、任意のy,wに関して `fboolT x y = fboolT x w` が成り立つ。これは、`fboolT x y`は`y`に依存せずに決まる関数`t x`に等しいことを意味する。同様に、`fboolF x y`も`x`に依存せずに決まる関数`f y`に等しい。

```haskell
t, f :: x -> F x
t x = join $ (x ? _) ? zero
f y = join $ zero ? (_ ? y)
```

また、`ifP x = return x ? zero = (x ? x) ? zero` であるから、`join . ifP = t`が成り立つ。
同様に`join . unlessP = f`である。このため、`t, f`ともにその引数に依存した結果を返す関数である。

```
join $ fbool (t x) (t y)
 = join $ fbool (join $ (x ? _) ? zero) (join $ (y ? _) ? zero)
 = join . fmap join $ ((x ? _) ? zero) ? ((y ? _) ? zero)
   -- 結合則を用いる
 = join . join $ ((x ? _) ? zero) ? ((y ? _) ? zero)
 = join $ (x ? _) ? zero
 = t x

-- 同様の計算により：

join $ fbool (t x) (t y) = t x
join $ fbool (t x) (f y) = x ? y
join $ fbool (f x) (t y) = zero
join $ fbool (f x) (f y) = f y

join $ t x ? (z ? w)
 = join $ fbool (join $ (x ? _) ? zero) (join . return $ z ? w)
 = join . fmap join $ ((x ? _) ? zero) ? (return $ z ? w)
 = join . join $ ((x ? _) ? zero) ? (return $ z ? w)
 = join $ (x ? _) ? (z ? w)
 = x ? w

-- 同様の計算により：

join $ f y ? (z ? w) = f w
join $ (x ? y) ? t z = t x
join $ (x ? y) ? f w = x ? w


join $ t (x ? y)
 = join . join $ ((x ? y) ? _) ? zero
 = join . fmap join $ ((x ? y) ? _) ? zero
 = join $ (join $ (x ? y) ? _) ? join zero
 -- _ = (_ ? _)
 = join $ (x ? _) ? zero
 = t x

join $ f (z ? w) = f w

join $ t x ? zero
 = join $ (join $ (x ? _) ? zero) ? (join zero)
 = join . fmap join $ ((x ? _) ? zero) ? zero
 = join . join $ ((x ? _) ? zero) ? zero
 = join $ t (x ? _)
 = t x

join $ zero ? t x
 = join $ zero ? (join $ (x ? _) ? zero)
 = join . fmap join $ zero ? ((x ? _) ? zero)
 = join . join $ zero ? ((x ? _) ? zero)
 = join $ f zero
 = zero

join $ zero ? f y = f y

join $ t (t x)
 = join $ t (join $ (x ? _) ? zero)
 = join . fmap join $ t ((x ? _) ? zero)
 = join . fmap join . join $ (((x ? _) ? zero) ? _) ? zero
 = join . join . fmap join $ (((x ? _) ? zero) ? _) ? zero
 = join . join $ (join $ ((x ? _) ? zero) ? _) ? join zero
 = join . join $ ((x ? _) ? _) ? zero
 = join . fmap join $ ((x ? _) ? _) ? zero
 = join $ (join $ (x ? _) ? _) ? zero
 = join $ (x ? _) ? zero
 = t x

join $ f (f x) = f x

join $ t (f x)
 = join $ t (join $ zero ? (_ ? x))
 = join . join $ t (zero ? (_ ? x))
 = join . join . join $ ((zero ? (_ ? x)) ? _) ? zero
 = join . join $ (join $ (zero ? (_ ? x)) ? _) ? zero
 = join . join $ (zero ? _) ? zero
 = zero

join $ f (t x) = zero

```

いま、`t :: forall x. x -> F x` はその引数に依存するので、`t x = L _` ではありえない。`F x`のコンストラクタが用いる`x`型の値の数は0か2以上なので、次の関数`t2`が存在して、`t2 x y`は`x`,`y`の両方に依存する。

```haskell
t2 :: forall x. x -> x -> F x
t2 x x = t x
```

ここで、`join`が`t2`に対してどう振る舞うか検討する。次の2つの等式がすぐにわかる。

```haskell
join $ t2 x y ? t2 x y
 = join $ return (t2 x y)
 = t2 x y

join $ t2 x x ? t2 y y
 = join $ t x ? t y
 = t x
```

したがって、次式が成り立つ。

```haskell
join $ t2 x y ? t2 z w
 = t2 x y
```

これを用いて、

```haskell
join . join $ (t2 x y ? zero) ? (zero ? t2 z w)
 = join $ t2 x y ? t2 z w
 = t2 x y

join . fmap join $ (t2 x y ? zero) ? (zero ? t2 z w)
 = join $ (join $ t2 x y ? zero) ? zero
 = join $ (join $ t2 x y ? zero) ? join zero
 = join . fmap join $ (t2 x y ? zero) ? zero
 = join . join $ (t2 x y ? zero) ? zero
 = join $ t (t2 x y)

join $ t (t2 x y) = t2 x y
```

```haskell
join $ t2 (t2 x y) (t2 x y)
 = join $ t (t2 x y)
 = t2 x y

join $ t2 (t2 x x) (t2 y y)
 = join $ t2 (t x) (t y)
 = join $ t2 (join $ (x ? _) ? zero) (join $ (y ? _) ? zero)
 = join . fmap join $ t2 ((x ? _) ? zero) ((y ? _) ? zero)
 = join . join $ t2 ((x ? _) ? zero) ((y ? _) ? zero)
 = join $ t2 (x ? _) (y ? _)
 = t2 x y

join $ t2 (x ? y) (x ? y)
 = join $ t (x ? y)
 = t x
 = t2 x x

join $ t2 (x ? x) (y ? y)
 = join . fmap return $ t2 x y
 = t2 x y

join $ t2 (x ? y) (z ? w)
 = t2 x z

-------------------------

join . join $ (t2 x y ? (z ? w)) ? zero
 = t (t2 x y)
 = t2 x y

join . fmap join $ (t2 x y ? (z ? w)) ? zero
 = join $ (join $ t2 x y ? (z ? w)) ? zero
 -- join $ t x ? (z ? w) = x ? w
 --   => join $ t2 x y ? (z ? w) = (x ? w) OR (y ? w)
 = 

```

