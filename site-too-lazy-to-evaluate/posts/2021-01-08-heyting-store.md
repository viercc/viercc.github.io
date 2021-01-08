---
title: ハイティング代数からApplicativeを作る
---

# 変なApplicative発見

[以前の記事](2020-07-25-found-counterexample.html)で、
次のApplicativeを発見しました。[^fn1]

```haskell
newtype H a = H (Bool, Bool -> a)
  deriving Functor

instance Applicative H where
  pure a = H (True, const a)
  H (x, f) <*> H (y, g) = H (x && y, fg)
    where fg t = f (t && (x ===> y)) (g (t && x))

-- | "x implies y" operator
(===>) :: Bool -> Bool -> Bool
x ===> y = not x || y

infixr 2 ===>
```

まず、これは実際にApplicativeになっていることを、計算で確かめてみます。

* 左単位 -- `pure f <*> b = fmap f b`

  ```haskell
  pure f <*> b
     = H (True, const f) <*> H (y, g)
     = H (True && x, fg)
        where
          fg t = const f (t && ____) (g (t && True))
               = f (g (t && True))
               = (f . g) (t && True)
      -- True is the unit of &&
    = H (x, f . g)
    = fmap f b
  ```

* 右単位 -- `a <*> pure b = fmap ($ b) a`

  ```haskell
  a <*> pure b
    = H (x, f) <*> H (True, const b)
    = H (x && True, fg)
        where
          fg t = f (t && (x  ===> True)) (const b ____)
               = f (t && (x  ===> True)) b
               = (($ b) . f) (t && (x ===> True))
      -- True is the unit of &&
      -- (_ ===> True) == True
    = H (x, ($ b) . f)
    = fmap ($ b) a
  ```

* 結合 -- `a <*> (b <*> c) = (.) <$> a <*> b <*> c`

  ```haskell
  a = H (x, f)
  b = H (y, g)
  c = H (z, h)

  a <*> (b <*> c)
    = H (x, f) <*> (H (y, g) <*> H (z, h))
    -- 細かい計算省略
    = H (x && y && z, f_gh)
        where
          f_gh t = f (t && x_yz) (g (t && x_y_z) (h (t && xy_z))
          x_yz  = (x ===> y && z)
          x_y_z = x && (y ===> z)
          xy_z  = x && y

  (.) <$> a <*> b <*> c
    = H (x, (.) . f) <*> H (y, g) <*> H (z, h)
    -- 細かい計算省略
    = H (x && y && z, fg_h)
        where
          f_gh t = f (t && x_yz) (g (t && x_y_z) (h (t && xy_z))
          x_yz  = ((x && y) ===> z) && (x ===> y)
          x_y_z = ((x && y) ===> z) && x
          xy_z  = x && y
  ```

  以下の等式はきちんと成り立っているので、結合則も成り立っています。
  
  * `x ===> (y && z)  =  ((x && y) ===> z) && (x ===> y)`
  * `x && (y ===> z)  =  ((x && y) ===> z) && x`

さて、ここまでの証明で、

* `Bool`が`&&`を積、`True`を単位元とするモノイドであること
* `x ===> True = True`
* 結合則を示すのに必要だった次の2つ
  * `x ===> (y && z)  =  ((x && y) ===> z) && (x ===> y)`
  * `x && (y ===> z)  =  ((x && y) ===> z) && x`

以外の性質は用いていません。となれば、
`Bool`の代わりに、同じ性質を満たす型`s`と演算`&&, 1, ===>`によって、
`H`を一般化することができそうです。

"かつ"と"ならば"を持つ代数としてすぐ思い浮かぶものには、
ハイティング代数([Wikipedia](https://en.wikipedia.org/wiki/Heyting_algebra#Category-theoretic_definition))
があります。この証明で使った等式は、`Bool`を含め、どんなハイティング代数においても成り立つものです。[^fn2]

ハイティング代数の例には、次のようなものがあります。
"かつ、または、ならば"の記号を$\wedge, \vee, \to$としています。

1. どんなブール代数も、$x \to y = \neg x \wedge y$と定義するとハイティング代数になります。
2. 最大元 $\top$ と最小元 $\bot$ を持つ全順序つき集合 $X$ に対して、次のように定めた演算によって
   $X$はハイティング代数になります。

   * $x \wedge y = \min \{x, y\}$
   * $x \vee y = \max \{x, y\}$
   * $x \le y$ のとき $x \to y = \top$
   * $x > y$ のとき $x \to y = y$ 

3. ある集合 $U$ の部分集合$X$のうち、空集合であるか、$U \setminus X$が有限集合になるもの集合$\mathrm{Cofin}(U)$
   を考えます。
  
   $$
   \mathrm{Cofin}(U) = \left\{ \emptyset \right\} \cup \left\{ X \subset U \mid \text{$U \setminus X$ is finite set} \right\}
   $$
  
   $\mathrm{Cofin}(U)$は、$U$のべき集合$\mathcal{P}(U)$からなるハイティング代数の部分代数です。
  
   * $\mathcal{P}(U)$はブール代数で、したがって1.の方法でハイティング代数になります。

2.や3.のハイティング代数を使ってできるApplicativeがどんな物なのか確認してみます。

```haskell
newtype Hord x a = Hord (x, x -> a)
  deriving (Functor)

instance (Ord x, Bounded x) => Applicative (Hord x) where
  pure a = Hord (maxBound, const a)
  Hord (x, f) <*> Hord (y, g) = Hord (min x y, fg)
    where x_to_y | x <= y    = maxBound
                 | otherwise = y
          fg t = f (min t x_to_y) (g (min t x))
```

--------

[^fn1]: 以降の議論のわかりやすさのため左右を入れ替える等しています

[^fn2]: 定理として次の3式は認めておくものとします。適当な教科書にあたれば証明があると思うので。
    
    $$
    \begin{align}
    x \to (y \wedge z) &= (x \to y) \wedge (x \to z)\\
    x \wedge (x \to y) &= x \wedge y\\
    (x \wedge y) \to z &= x \to (y \to z)
    \end{align}
    $$
    
    これを使えば、結合則を示すのに必要だった等式は次の通り。
    
    $$
    \begin{align}
    ((x \wedge y) \to z) \wedge (x \to y)
      &= (x \to (y \to z)) \wedge (x \to y)\\
      &= x \to ((y \to z) \wedge y)\\
      &= x \to (y \wedge z)\\
    ((x \wedge y) \to z) \wedge x
      &= (x \to (y \to z)) \wedge x\\
      &= x \wedge (y \to z)
    \end{align}
    $$
