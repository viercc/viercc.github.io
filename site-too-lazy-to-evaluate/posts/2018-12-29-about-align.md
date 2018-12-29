---
title: 型クラスAlignについて
---

型クラス[`Align`](http://hackage.haskell.org/package/these-0.7.5/docs/Data-Align.html)は`Kleisli Maybe`から`->`へのlax monoidal functorだとドキュメントに書いてあるけど、それは違うんじゃないかという事についてです。

Applicativeによく似た構造をしているAlignですが、その意味をきちんと定義するAlign則はまだ未完成で、
先日それに関して作者のGitHubにIssueを投げました。
この記事はその準備として書き始めたものですが、せっかくなのでここで公開することししました。

## `Align` って何

`Align`は、theseパッケージのData.Alignで定義されている型クラスです。

``` haskell
class Functor f => Align f where
    nil :: f a
    align :: f a -> f b -> f (These a b)
```

ドキュメントにはこんな事が書いてあります。（私訳）

> ... If your functor is actually a functor from `Kleisli Maybe` to `Hask` (so it supports `maybeMap :: (a -> Maybe b) -> f a -> f b)`, then an `Align` instance is making your functor lax monoidal w.r.t. the cartesian monoidal structure on `Kleisli Maybe`, because `These` is the cartesian product in that category (`a -> Maybe (These b c) ~ (a -> Maybe b, a -> Maybe c)`).

> もしその関手が現に`Kleisli Maybe`から`Hask`への関手であれば（すなわち`maybeMap :: (a -> Maybe b) -> f a -> f b`を持てば）、\[訳補:その関手の\]`Align`のインスタンスは、その関手を`Kleisli Maybe`上の直積モノイド構造に対してlax monoidalにします。なぜなら、`These`はその圏における直積だからです(`a -> Maybe (These b c) ~ (a -> Maybe b, a -> Maybe c)`)。

割と意味不明な圏論用語が多かったので、nlabというサイトを参考になんとなく調べたらなんとなく意味がわかった気がしました。
でも、私の理解した限りではこのドキュメントは間違っています。なので、圏論をHaskellに翻訳しながら「なぜ間違っているのか」説明しようと思います。

* 圏、対象、射\[category, object, morphism\]
* 直積\[cartesian product\]
* モノイド圏\[monoidal category\]
* 関手\[functor\]
* lax monoidal関手\[lax monoidal functor\]

をHaskellに翻訳しながら説明します。（自分がHaskellに翻訳しないと理解できないため）

### 圏、対象、射

ここでは、圏とは次の型クラス`Category`のインスタンス`cat :: k -> k -> Type`を、
対象とはカインド`k`の型を、射とは`cat x y :: Type`型の値という意味*だとします*。
混乱を避けるために繰り返して言うと、対象は*型*で、射は*値*です。

``` haskell
class Category (cat :: k -> k -> Type) where
    id :: cat x x
    (.) :: cat y z -> cat x y -> cat x z
```

また、射の結合演算子 `.` は結合法則を満たし、`id`は単位元になっているとします。すなわち

```
    (f . g) . h = f . (g . h)
    f . id = id . f = f
```

が成り立っているものとします。

この記事で使う圏として`Hask`と`Kleisli m`を挙げておきます。

``` haskell
type Hask = (->)

instance Category Hask where
    id :: x -> x
    id = Prelude.id

    (.) :: (y -> z) -> (x -> y) -> x -> z
    (.) = (Prelude..)

newtype Kleisli m a b = Kl (a -> m b)

instance (Monad m) => Category (Kleisli m) where
    id :: Kleisli m x x     --  ~  x -> m x
    id = Kl return

    (.) :: Kleisli m y z -> Kleisli m x y -> Kleisli m x z
              -- ~ (y -> m z) -> (x -> m y) -> x -> m z
    Kl f . Kl g = Kl $ f <=< g
```

### 直積

圏論での直積は、集合の直積を一般化したような概念です。

Haskellで言うなら、ある圏(Category)の対象2つをとって別の対象を返す(型レベルの)関数で、
集合の直積みたいな性質を表すいくつかの射を持つものです。
3個、4個、有限のn個の対象の直積は、適当に2個の直積を組み合わせればよいです。
どんな順番でどのように積をとっても、すべて同型になると示すことができます。
また、"0個の対象の直積"として終対象という特別な対象も考えます。

``` haskell
class Category cat => CartesianProduct (cat :: k -> k -> *) where
    type CP cat :: k -> k -> k
    type Terminal cat :: k
    
    fst :: cat (CP cat x y) x
    snd :: cat (CP cat x y) y
    pair :: cat a x -> cat a y -> cat a (CP cat x y)
    term :: cat a (Terminal cat)
    
    -- fst . pair f g = f
    -- snd . pair f g = g
    -- pair (fst . f) (snd . f) = f
    -- term . f = term

(***) :: (CartesianProduct cat, p ~ CP cat) => cat x x' -> cat y y' -> cat (p x y) (p x' y')
f *** g = pair (f . fst) (g . snd)

assoc :: (CartesianProduct cat, p ~ CP cat)
      => cat (p x (p y z)) (p (p x y) z)
assoc = (fst `pair` (fst . snd)) `pair` (snd . snd)
```

`Hask`は直積を持ちます。`(,)`のことです。

``` haskell
instance CartesianProduct Hask where
    type CP Hask = (,)
    type Terminal Hask = ()
    
    fst :: (x, y) -> x
    fst = Prelude.fst
    
    snd :: (x, y) -> y
    snd = Prelude.snd
    
    pair :: (a -> x) -> (a -> y) -> (a -> (x, y))
    pair f g a = (f a, g a)

    term :: a -> ()
    term _ = ()

-- (***) :: (a -> a') -> (b -> b') -> (a,b) -> (a',b')
-- assoc :: (a, (b, c)) -> ((a, b), c)
```

`Kleisli m` は一般の`Monad m`については直積を持ちません。型を合わせるだけならできますが`fst . pair f g = f`のような法則を満たしません。ただし、`m ~ Maybe`のときは`These`を使えばできます。

``` haskell
instance CartesianProduct (Kleisli Maybe) where
    type CP (Kleisli Maybe) = These
    type Terminal (Kleisli Maybe) = Void
    
    fst :: Kleisli Maybe (These x y) x
        -- These x y -> Maybe x
    fst = Kl getThis
      where getThis (This x) = Just x
            getThis (That y) = Nothing
            getThis (These x y) = Just x
    
    snd :: Kleisli Maybe (These x y) y
        -- These x y -> Maybe y
    snd = Kl getThat
      where getThat (This x) = Nothing
            getThat (That y) = Just y
            getThat (These x y) = Just y

    pair :: Kleisli Maybe a x           --    (a -> Maybe x)
         -> Kleisli Maybe a y           -- -> (a -> Maybe y)
         -> Kleisli Maybe a (These x y) -- -> (a -> Maybe (These x y))
    pair (Kl f) (Kl g) = Kl $ \a -> pairMaybes (f a) (g a)
     
    term :: Kleisli Maybe a Void
    term = Kl $ \_ -> Nothing

pairMaybes :: Maybe a -> Maybe b -> Maybe (These a b)
pairMaybes x y = case (x,y) of
    (Nothing, Nothing) -> Nothing
    (Just x,  Nothing) -> Just (This x)
    (Nothing, Just y)  -> Just (That y)
    (Just x,  Just y)  -> Just (These x y)

-- (***) :: (a -> Maybe a') -> (b -> Maybe b') -> These a b -> Maybe (These a' b')
-- assoc :: These a (These b c) -> Maybe (These (These a b) c)

```

これが例の`a -> Maybe (These b c) ~ (a -> Maybe b, a -> Maybe c)`の出番でした。

### モノイド圏

モノイド圏とは、圏`cat`に、追加で対象`1`と対象の上の演算子`⊗`が定義され、いろいろな条件を満たすもののことですが、`CartesianProduct`な圏にとっては、[終対象と直積がこの条件を満たすらしい](https://ncatlab.org/nlab/show/cartesian+monoidal+category)ので、この記事では`1 = Terminal cat`, `⊗ = CP cat`と置かれているものとします。

### 関手

関手\[functor\]とは、2つの圏のあいだの"準同型"みたいな関係です。圏`C`から圏`D`への関手`F`は、

* `C`の対象を`D`の対象に写す写像`F`
* `C`の射`C x y`を`D`の射`D (F x) (F y)`に写す写像`map`

つまり次のような型クラスです。

``` haskell
class (Category (Dom f), Category (Cod f)) => Functor (f :: j -> k) where
    type Dom f :: j -> j -> Type
    type Cod f :: k -> k -> Type
    
    map :: Dom f x y -> Cod f (f x) (f y)
    
    -- map id = id
    -- map (f . g) = map f . map g
```

例をあげると、今定義した方ではなくていつも使っている方の`Functor`は`Hask`から`Hask`への関手です。
いつも使っている方の`Prelude.Functor`を使うというラッパー`HaskF`を定義しましょう。

``` haskell
newtype HaskF f a = HaskF (f a)

instance (Prelude.Functor f) => Functor (HaskF f) where
    type Dom (HaskF f) = Hask
    type Cod (HaskF f) = Hask

    map :: (a -> b) -> (HaskF f a -> HaskF f b)
    map f (HaskF x) = HaskF (Prelude.fmap f x)
```

また、`[]`や`Map k`は(HaskからHaskへの関手でもありますが)、`Kleisli Maybe`から`Hask`への関手なのです！

``` haskell
instance Functor [] where
    type Dom [] = Kleisli Maybe
    type Cod [] = Hask
    
    map :: Kleisli Maybe a b -> [a] -> [b]
    map (Kl f) = Data.Maybe.mapMaybe f
    
    -- map id = Data.Maybe.mapMaybe return = id
    -- map (f . g) = Data.Maybe.mapMaybe (f <=< g)
    --             = Data.Maybe.mapMaybe f . Data.Maybe.mapMaybe g
    --             = map f . map g

instance (Ord k) => Functor (Map k) where
    type Dom (Map k) = Kleisli Maybe
    type Cod (Map k) = Hask

    map :: Kleisli Maybe x y -> (Map k x -> Map k y)
    map (Kl f) mx = Map.mapMaybe f mx

    -- Map.mapMaybe return = Map.mapMaybe Just = id
    -- Map.mapMaybe (f <=< g) = Map.mapMaybe f . Map.mapMaybe g
```

一般的に言って、[Filterable](http://hackage.haskell.org/package/witherable-0.3/docs/Data-Witherable.html#t:Filterable)
のインスタンスは`Kleisli Maybe`から`Hask`への関手です。Filterable則をじっと眺めたら、`Kleisli Maybe`から`Hask`への`Functor`則
だということがわかるでしょう。

### lax monoidal 関手

(Lax) monoidal 関手は、モノイド圏からモノイド圏への関手で、その構造を保つためのいくつかの条件を満たすものです。今は終対象と直積からなるモノイドだけを考えていたので、それを織り込み済みで書くなら、

``` haskell
class (CartesianProduct (Dom f), CartesianProduct (Cod f), Functor f) =>
      LaxMonoidalFunctor f where
    unit :: Cod f (Terminal (Cod f)) (f (Terminal (Dom f)))
    multiply :: Cod f (CP (Cod f) (f a) (f b)) (f (CP (Dom f) a b))
    
    -- [Naturailty] multiply . (map f *** map g) = map (f *** g) . multiply
    -- [Left Unit]  map snd . multiply . pair (unit . term) id = id
    -- [Right Unit] map fst . multiply . pair id (unit . term) = id
    -- [Associativity] map assoc . multiply . id *** multiply = multiply . multiply *** id . assoc
```

ややこしい！！具体例を考えないと頭が爆発しそうなので、`Hask`から`Hask`への関手の場合を考えましょう。`HaskF`を再び登場させます。

``` haskell
instance (???) => LaxMonoidalFunctor (HaskF f) where
    unit :: -- Cod f (Terminal (Cod f)) (HaskF f (Terminal (Dom f))) =
            -- Hask (Terminal Hask) (HaskF f (Terminal Hask)) =
            () -> HaskF f ()
            -- ~ f ()
    
    multiply :: -- Cod f (CP (Cod f) (HaskF f a) (HaskF f b)) (f (CP (Dom f) a b)) =
                -- Hask (CP Hask (HaskF f a) (HaskF f b)) (HaskF f (CP Hask a b)) = 
                (HaskF f a, HaskF f b) -> HaskF f (a, b)
                 -- ~ f a -> f b -> f (a,b)
```

[実はこれって`Applicative`なんです。](https://wiki.haskell.org/Typeclassopedia#Alternative_formulation)

``` haskell
instance (Applicative f) => LaxMonoidalFunctor (HaskF f) where
    unit _ = HaskF (pure ())
    
    multiply (HaskF fa, HaskF fb) = HaskF $ (,) <$> fa <*> fb
```

そしてなんと、`Kleisli Maybe`から`Hask`への関手としての`Map k`も`LaxMonoidalFunctor`になって、
そのメソッドは`Align`クラスを使って定義できるのです！

``` haskell
instance (Ord k) => LaxMonoidalFunctor (Map k) where
    unit :: --    Cod f (Terminal (Cod f)) (f (Terminal (Dom f)))
            --  = Terminal Hask -> Map k (Terminal (Kleisli Maybe)) =
            () -> Map k Void
    unit _ = Data.Align.nil
    
    multiply :: -- Cod f (CP (Cod f) (f a) (f b)) (f (CP (Dom f) a b))
                -- = Hask (CP Hask (Map k a) (Map k b)) (Map k (CP (Kleisli Maybe) a b)) =
                (Map k a, Map k b) -> Map k (These a b)
    multiply (ma, mb) = Data.Align.align ma mb
```

やったか！？

## Align ≠ LaxMonoidalFunctor

実はやってないんです。`[]`はHaskからHaskへの関手でもありますが、先程挙げた例に示すとおり`Kleisli Maybe`から`Hask`への関手と見なすこともできます。

しかし、`Align`を使った次の定義は法則を満たしません。

``` haskell
instance LaxMonoidalFunctor [] where
    unit :: () -> [Void]
    unit _ = Data.Align.nil
    
    multiply :: ([a], [b]) -> [These a b]
    multiply (as, bs) = Data.Align.align as bs
```

`LaxMonoidalFunctor`則の

```
    multiply . (map f *** map g) = map (f *** g) . multiply
```

を満たさないのです！つまり、

> ... an `Align` instance is making your functor lax monoidal w.r.t. the cartesian monoidal structure on `Kleisli Maybe` ...

という説明は**現状に合っていない**ということです。

## 結論

`Data.Align`のドキュメンテーションには、「`Align`は`Kleisli Maybe`から`Hask`へのlax monoidal関手を表す」
という格好いい一文があり、それがもし本当ならAlign則のもっと適切なバージョンを導くといったうれしい点がありました。

しかし、現状`Map k`や`HashMap k`といったインスタンスだけがlax monoidal関手を表しており、
`[]`や`Seq`などはそうなっていません。つまり、現状を追認する形でAlign則を定義しようとするなら、
*`Kleisli Maybe`から`Hask`へのlax monoidal関手*というアプローチは取れないということです。

