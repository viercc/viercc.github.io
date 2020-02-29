---
title: 可換なモナドとは？
---

## `ListT`の醜名

よく知られた話として、モナド変換子 `ListT`（[ドキュメント](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-List.html#t:ListT)）
が`Monad`則を満たしていないという話があります。

`ListT`は、あまり本質的でない部分を除くと、以下のように定義されています。

```haskell
newtype ListT m a = ListT { runListT :: m [a] }

instance (Functor m) => Functor (ListT m) where {- 省略 -}
instance (Applicative m) => Applicative (ListT m) where {- 省略 -}

instance (Monad m) => Monad (ListT m) where
    return a = ListT $ return [a]
    ListT mta >>= k = ListT $ fmap concat $ mta >>= traverse (runListT . f)
```

しかし、`instance Monad m => Monad (ListT m)` は正当なインスタンスではありません。
どんな `m` に対しても`ListT m`が真にMonadである―Monad則を満たす―わけではないからです。
（そのため、`Control.Monad.List`はモジュール全体がdeprecatedです。）

Monadとして破綻していることを実際に示すことも簡単にできます。

```
>>> import Control.Monad.List
>>> :set -Wno-deprecations
>>> :{
    purr :: String -> ListT IO ()
    purr str = ListT (putStr str >> return [(), ()]) 
    :}
>>> runListT $ purr "a" >> (purr "b" >> purr "c")
abccbcc[(),(),(),(),(),(),(),()]
>>> runListT $ (purr "a" >> purr "b") >> purr "c"
abbcccc[(),(),(),(),(),(),(),()]
```

副作用として出力された文字の順番に注目してください。カッコを付け替えただけなのに順番が違いますね？
Monad則の一つ、結合法則を満たしていません。

さて、`ListT`のドキュメントにはこんなことが書かれています。

> _Note:_ this does not yield a monad unless the argument monad is commutative.
> 
> _注意:_ 引数のモナドが可換でない限り、これはMonadにはならない。

裏を返せば、「引数のモナド`m`が可換なときに限り、`ListT m`はMonadになる」ということです。

さて、「モナドが可換である」って、聞いたことあります？私は、「なんとなく言いたいことはわかるけど、
ちょっと曖昧じゃない？」と感じていました。例えば、ある2項演算`op :: (X, X) -> X`が可換であると言うとき、ふつうは

```haskell
swap :: (x, y) -> (y, x)
swap (x, y) = (y, x)
```

のように、"引数の順番を入れ替える"写像を使って、`op . swap = op`のように定義します。しかし、`Monad`の"2項演算"は
`join :: forall a. m (m a) -> m a`です。この"引数の順番を入れ替える"ことは、一般にはできません。
では、Monadが可換であるという条件は、どう定義すればいいのでしょうか？

## 可換なモナド \#とは

ググってみましょう。

* [HaskellWikiでの定義](https://wiki.haskell.org/Monad#Commutative_monads)

  `Monad m`が可換であるとは、任意の`actA :: m a, actB :: m b, m :: a -> b -> m c`に対して、
  以下の等式が成り立つことを意味します。
  
  ```haskell
  do { a <- actA; b <- actB; m a b }
    =
  do { b <- actB; a <- actA; m a b }
  ```
  
  Monad則を使えば、これは「任意の`f :: a -> b -> c`に対して `liftM2 f actA actB = liftM2 (flip f) actB actA`」
  と同値です。
  
  どんなMonadも、その親クラスのApplicativeとの関係として、`liftA2 = liftM2`が要求されるため、
  「`liftA2 f actA actB = liftA2 (flip f) actB actA`」とも同じことです。
  
  これで、Monadが可換である条件は、`Applicative`の言葉だけで書けました。
  標語的に、「`m`が可換であるとは、`Applicative`として可換である」とでも言いましょう。

* [Wikipedia](https://en.wikipedia.org/wiki/Strong_monad)
  
  一般の（対称モノイダル）圏で考えるために色々書いてありますが、Haskellの`Monad`の場合だけを考えればそんなに難しいことは書いていないので、エイヤと翻訳してしまいます。
  
  `Monad`である`T`が可換であるとは、次の関数を使って・・・
  
  ```haskell
  left_strength :: (a, T b) -> T (a, b)
  left_strength (a, tb) = fmap (a, ) tb
  
  right_strength :: (T a, b) -> T (a, b)
  right_strength = fmap swap . left_strength . swap
    where swap (x, y) = (y, x)
  ```
  
  この等式が成り立つことをいいます。
  
  ```haskell
  join . fmap right_strength . left_strength :: (T a, T b) -> T (a, b)
    =
  join . fmap left_strength . right_strength :: (T a, T b) -> T (a, b)
  ```
  
  よくよく読めば、これもHaskellWikiの定義と同値だとわかります。実際、`=`の両辺をゴリゴリ変形すると、次のようにできます。

  ```haskell
  \(ta, tb) -> do { b <- tb; a <- ta; return (a, b) }
    =
  \(ta, tb) -> do { a <- ta; b <- tb; return (a, b) }
  ```

はい、これで「Monadが可換である」という言葉の意味が「Applicativeとして可換である」だったことがわかりました。

## 証明しよう、「モナド`m`が可換」 ⇒ 「`ListT m`がモナド則を満たす」

「モナド`m`が可換」 ⇒ 「`ListT m`がモナド則を満たす」は、実際に証明できるはずなので、やってみましょう。

次の2つのステップに分けて進めます。

1. 「モナド`m`が可換」 ⇒ 「`join'`がApplicative準同型」
2. 「`join'`がApplicative準同型」 ⇒ 「`ListT m`がモナド則を満たす」

ここで、`join'`は、`m`の`Monad`を使って書かれる次の関数です。

```haskell
join' :: Monad m => forall a. Compose m m a -> m a
join' = join . runCompose
```

`Compose`については[Data.Functor.Compose](https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Functor-Compose.html)を参照して下さい。

Applicative準同型とは、[Data.Traversable](https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Traversable.html#t:Traversable)のドキュメントでしか見たことがない、でもまあ、そうなるよねっていう感じのする、
Applicativeの間の自然変換です（いいかげん）。

> an _applicative transformation_ is a function
> 
> `t :: (Applicative f, Applicative g) => f a -> g a`
> 
> preserving the Applicative operations, i.e.
> 
> * `t (pure x) = pure x`
> * `t (x <*> y) = t x <*> t y`

### 「モナド`m`が可換」 ⇒ 「`join'`がApplicative準同型」

`join'`が確かにApplicative準同型であることは、単に計算すれば出ます。

1. `join' (pure x :: Compose m m a) = (pure x :: m a)`
   
   ```haskell
   join' (pure x)
     = join' $ Compose (pure (pure x))
     = join . runCompose $ Compose $ pure (pure x)
     = join $ pure (pure x)
       -- pure = return に注意
     = pure x
   ```

2. `join' (x <*> y) = t x <*> t y`
   
   `x = Compose mmf :: Compose m m (a -> b), y = Compose mma :: Compose m m a`とおく。
   
   ```haskell
   join' (Compose mmf <*> Compose mma)
     = join' $ Compose (liftA2 (<*>) mmf mma)
     = join . runCompose $ Compose (liftA2 (<*>) mmf mma)
     = join $ liftA2 (<*>) mmf mma
       -- liftA2 = liftM2, (<*>) = ap
     = do mf <- mmf
          ma <- mma
          mf <*> ma
     = do mf <- mmf
          ma <- mma
          f <- mf
          a <- ma
          return (f a)
       -- m が可換であることを使う
     = do mf <- mmf
          f <- mf
          ma <- mma
          a <- ma
          return (f a)
     = do f <- do { mf <- mmf; mf }
          a <- do { ma <- mma; ma }
          return (f a)
     = do f <- join mmf
          a <- join mma
          return (f a)
     = join mmf <*> join mma
     = join' (Compose mmf) <*> join' (Compose mma)
   ```

## 「`join'`がApplicative準同型」 ⇒ 「`ListT m`がモナド則を満たす」

[証明は長過ぎるので別のページに移しました。](./2020-02-29-commutative-monad-appendix.html)

## 余談

余談ですが、上で示したことの逆も示せます。

* 「モナド`m`が可換」 ⇐ 「`join'`がApplicative準同型」

なので、「`join'`がApplicative準同型」も、「モナド`m`が可換」の定義として使えます。

```haskell
f :: a -> b -> c
ma :: m a
mb :: m b

mf = f <$> ma :: m (b -> c)

-- join'が準同型であることを使う
join' $ Compose (pure mf) <*> Compose (fmap pure mb)
  = join' (Compose (pure mf)) <*> join' (Compose (fmap pure mb))
  = join (pure mf) <*> join (fmap pure mb)
  = mf <*> mb
  = f <$> ma <*> mb
  = liftM2 f ma mb

-- Applicative (Compose m m) を使う
join' $ Compose (pure mf) <*> Compose (fmap pure mb)
  = join' $ Compose (liftA2 (<*>) (pure mf) (fmap pure mb))
  = join $ liftA2 (<*>) (pure mf) (fmap pure mb)
  = join $ fmap (mf <*>) (fmap pure mb)
  = join $ fmap (\b -> mf <*> pure b) y
  = join $ fmap (\b -> fmap ($ b) mf) mb
  = mb >>= \b -> fmap ($ b) mf
  = mb >>= \b -> fmap (($ b) . f) ma
  = mb >>= \b -> fmap (flip f b) ma
  = liftM2 (flip f) mb ma

-- したがって、mは可換なモナドである。
liftM2 f ma mb = liftM2 (flip f) mb ma
```

