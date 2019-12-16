---
title: (主張3)の証明が改善の余地ありだったので修正
---

# 主張

ある多項式Functor`F`が `F(x) ~ c + x^2 * G(x)`(`|c| >= 1, G(x) ~/~ 0`)と書けるならば、`F`の`Monad`のインスタンスは存在しない。

例:以下のFunctorには`Monad`のインスタンスを与えることができない。

* `F(x) ~ 1 + x^2`
* `F(x) ~ 3 + x^2 + x^4`

# 証明

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

以下の事実がわかる。

* 任意の`i`に対して`at i x`は`x`に依存する。

これを示すため、いま、ある`i :: N`において`at i x`が`x`に依存しないと仮定する。
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
よって、仮定したことの否定、任意の`i :: N`に対して`at i x`は`x`に依存する

また、`at i`に関するさまざまな性質が、`Monad`則を仮定すると得られる。

* `join $ at i (U f) = at i (f i)` ... (at-U)

```haskell
join $ at i (U f)
 = join . join $ U $ \j -> if i == j then return (U f) else zero
 = join $ U $ \j -> if i == j then (join . return) (U f) else join zero
   -- join . return = id   = join . fmap return
   -- join zero     = zero = join (return zero)
 = join $ U $ \j -> if i == j then (join . fmap return) (U f) else join (return zero)
 = join . fmap join $ U $ \j -> if i == j then (join . fmap return) (U f) else join (return zero)
   -- 結合則
 = join . join $ U $ \j -> if i == j then fmap return (U f) else return zero
   -- fmap return (U f) = U (return . f)
   -- return zero = U (const zero)
 = join . join $ U $ \j -> if i == j then U (return . f) else U (const zero)
 = join . join $ U $ \j -> U (\k -> if i == j then return (f k) else zero
   -- joinUU
 = join $ U $ \j -> if i == j then return (f j) else zero
   -- i == j より j を i に置換
 = join $ U $ \j -> if i == j then return (f i) else zero
 = at i (f i)
```

さらに、次の補助関数`squash, hole`を定義する。

```haskell
squash :: N -> (forall x. x -> F x) -> F N
squash i u = join $ U $ \j -> if i == j then u j else return j

hole :: forall x. N -> F x -> F x
hole i fx = join $ U $ \j -> if i == j then zero else fx
```

* `squash i (at i) = U id` .. (squash-at)

```haskell
squash i (at i)
 = join $ U $ \j -> if i == j then at i j else return j
 = join $ U $ \j ->
     if i == j
       then join $ U (\k -> if i == k then return j else zero)
       else join . return . return $ j
 = join . fmap join $ U $ \j ->
     if i == j
       then U (\k -> if i == k then return j else zero)
       else U (\_ -> return j)
 -- 結合則 + joinU
 = join $ U $ \j ->
     if i == j
       then if i == j then return j else zero
       else return j
 = join $ U $ \j -> return j
 = join . fmap return $ U (\j -> j)
 = U id
```

* `hole i (at i x) = zero` ... (hole-at)

```haskell
hole i (at i x)
 = join $ U $ \j -> if i == j then zero else (at i x)
 = join $ U $ \j ->
     if i == j
       then zero
       else join $ U $ \k -> if i == k then return x else zero
   -- join . return = id
 = join $ U $ \j ->
     if i == j
       then join $ return zero
       else join $ U $ \k -> if i == k then return x else zero
 = join . fmap join $ U $ \j -> U $ \k ->
     if i == j
       then zero
       else if i == k then return x else zero
   -- 結合則 + joinUU
 = join $ U $ \j ->
     if i == j
       then zero
       else if i == j then return x else zero
 = join $ U $ \j -> zero
 = join $ return zero
 = zero
```

いま、`at i x`は`x`に依存するのであった。`return`のときと同様の議論によって、`at i x`が返すコンストラクタは2つ以上の`x`の値に依存することができるので、関数`con :: N -> x -> x -> F x`が存在して、`con i x y`は`x`と`y`の両方に依存し、
`con i x x = at i x`となるようにできる。さらに、次の式が成り立つ。

* `hole i (con i x y) = zero` ... (hole-con)

これは、`hole`が`x`に関して自然、すなわち`x`型の変数の内容に依存して処理を変えることがないことから
`hole i (con i x y)` と `hole i (con i x x) = hole i (at i x)` を区別できないことから、
(hole-at)を組み合わせるとわかる。

* `at i (con i x y) = con i x y` ... (at-con)

```haskell
join $ at i (con i x y)
 = join . join $ U $ \j -> if i == j then return (con i x y) else zero
   -- 結合則
 = join . fmap join $ U $ \j -> if i == j then return (con i x y) else zero
 = join $ U $ \j -> if i == j then join (return (con i x y)) else join zero
   -- (hole-con)より、
   -- join zero = zero = hole i (con i x y)
 = join $ U $ \j ->
     if i == j
       then join $ return (con i x y)
       else hole i (con i x y)
 = join $ U $ \j ->
     if i == j
       then join $ return (con i x y)
       else join $ U (\k -> if i == k then zero else con i x y)
 = join . fmap join $ U $ \j ->
     if i == j
       then return (con i x y)
       else U (\k -> if i == k then zero else con i x y)
 = join . fmap join $ U $ \j -> U $ \k ->
     if i == j
       then con i x y
       else if i == k then zero else con i x y
   -- 結合則 + joinUU
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
extra i x y f = join $ U $ \j -> if i == j then con i x y else return (f j)
```

`extra`の特別な場合について計算する。

```haskell
extra i (f i) (f i) f
 = join $ U $ \j -> if i == j then con i (f i) (f i) else return (f j)
 = join $ U $ \j -> if i == j then at i (f i) else return (f j)
 = join $ U $ \j -> if i == j then fmap f (at i i) else fmap f (return j)
 = join . fmap (fmap f) $ U $ \j -> if i == j then at i i else return j
   -- i == j より i と j を置換
   -- join . fmap (fmap f) = fmap f . join 
 = fmap f . join $ U $ \j -> if i == j then at i j else return j
 = fmap f $ squash i (at i)
   -- (squash-at)
 = fmap f $ U id
 = U f
```

`extra`は`x`に関して自然なので、任意の`x, y, f`に関して、
ある`g :: N -> x`を用いて`extra i x y f = U g`とならなければならない。
このことを用いると、次のような計算ができる。

```haskell
join $ at i (extra i x y f)
 = join $ at i (U g)
   -- (at-U)
 = at i (g i)
```

しかし、`extra`の定義にもとづいて別の計算を行うと、

```haskell
join $ at i (extra i x y f)
 = join . join $ U $ \j ->
     if i == j
       then extra i x y f
       else zero
   -- extraの定義, join . return = id
 = join . join $ U $ \j ->
     if i == j
       then join $ U (\k -> if i == k then con i x y else return (f k))
       else join (return zero)
 = join . join . fmap join $ U $ \j ->
     if i == j
       then U (\k -> if i == k then con i x y else return (f k))
       else return zero
 = join . join . fmap join $ U $ \j -> U $ \k ->
     if i == j
       then if i == k then con i x y else return (f k)
       else zero
   -- 結合則 + joinUU
 = join . join $ U $ \j ->
     if i == j
       then if i == j then con i x y else return (f j)
       else zero
 = join . join $ U $ \j -> if i == j then con i x y else zero
 = join $ at i (con i x y)
   -- (at-con)
 = con i x y
```

である。しかし、`at i (g i)`は`x,y`のうち高々一つにしか依存できないのに対し、`con i x y`は両方に依存する。

これは矛盾である。したがって、`Monad`則を満たすように`F`の`Monad`のインスタンスを与えることはできない。

# 疑問点

ただちょっとわからない点があって、`N`が無限であることを許したとき、`x == y`ならば`f x = f y`を保証できるような`(==) :: N -> N -> Bool`が定義できるか？という問題がある。

この証明は、`p x = True`をみたす`x`がちょうど1つだけ存在するような `p :: N -> Bool` が一つでもあれば、`(i ==)`の代わりにそれを使うように書き換えるのは難しくないはずなので、このような`p`が存在しないかもしれない、という問題といってもいい。

まず、`|N| >= 2`なる条件をHaskellで表現するなら、次の両方が成り立つことだ（と思う）。

* ある`inj :: Bool -> N`が存在して、任意の`X :: Type`, `f, g :: X -> Bool`に対して`inj . f = inj . g`ならば`f = g`
* ある`surj :: N -> Bool`が存在して、任意の`X :: Type`, `f, g :: Bool -> X`に対して`f . surj = g . surj`ならば`f = g`

しかし、これを満たすにもかかわらず、`(==)`が定義できないような型がある。先程の条件を満たす`p`も無い。

```haskell
newtype BitStream = BitStream (Bool, BitStream Bool)

inj :: Bool -> BitStream
inj x = BitStream (x, inj x)

surj :: BitStream -> Bool
surj (BitStream (x, _)) = x
```

ただ、`N = BitStream`のとき、`join`は全域関数にできないだろう。一般に、`N`が`(==)`が定義できない(or 条件を満たす`p`が無い)ような型ならば、`join`は全域関数にできないと言えるか？
