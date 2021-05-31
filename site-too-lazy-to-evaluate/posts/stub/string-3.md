---
title: ストリング図でMonad再入門(3)
published: 2021-05-31
---

[前回]、ストリング図を使って`StateT`モナド変換子のモナド則を証明しました。
今度は`ReaderT`,`WriterT`,`ExceptT`の3つについてやっていきます。

* [ReaderT](https://hackage.haskell.org/package/transformers-0.5.6.2/docs/Control-Monad-Trans-Reader.html#g:2)
* [WriterT](https://hackage.haskell.org/package/transformers-0.5.6.2/docs/Control-Monad-Trans-Writer-Lazy.html#g:2)
* [ExceptT](https://hackage.haskell.org/package/transformers-0.5.6.2/docs/Control-Monad-Trans-Except.html#g:2)

## 共通の構造

前回の記事までは、証明の方針は私が天下り的に与えていましたが、
今回は「発見的な」やり方で説明してみようと思います。

### WriterTの場合

まずは、`WriterT`の実装を眺めてみます。

```haskell
-- transformers パッケージのものとは（同型ですが）少し違います
newtype WriterT w m a = WriterT { runWriterT :: m (w, a) }

instance Functor m => Functor (WriterT w m) where {- 省略 -}

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  pure = pureWriter >>> pure >>> WriterT
    where
      pureWriter :: Monoid w => a -> (w, a)
      pureWriter a = (mempty, a) -- Writerモナド (w, ) のpure
  join = fmap runWriterT >>> runWriterT >>> joinT >>> WriterT
    where
      joinT :: (Monad m, Monoid w) => m (w, m (w, a)) -> m (w, a)
      joinT mwmwa =
        do (w, mwa) <- mwmwa
           (w', a) <- mwa
           return (w <> w', a)
```

ここで、`pure`は自然変換`pureWriter`, `pure`, `WriterT`の合成で書くことができていて、
ストリング図に書きやすそうです。
一方、`join`の実装に使った`joinT`は、もっと単純な自然変換の合成で書けてはいないようです。
`joinT`をうまいこと自然変換たちに分解してみましょう。

```haskell
-- Writerモナド(w, )のjoinが使えそうです
joinWriter :: Monoid w => (w, (w, a)) -> (w, a)
joinWriter (w, (w', a)) = (w <> w', a)

joinT :: (Monad m, Monoid w) => m (w, m (w, a)) -> m (w, a)
joinT = \mwmwa -> do
  (w, mwa) <- mwmwa
  (w', a) <- mwa
  return (w <> w', a)
= \mwmwa -> do
  (w, mwa) <- mwmwa
  fmap (\(w',a) -> (w <> w', a)) m
= \mwmwa -> mwmwa >>= \(w,mwa) -> mwa >>= \(w',a) -> return (w <> w', a)
= \mwmwa -> mwmwa >>= \(w,mwa) -> fmap (\(w',a) -> (w<>w',a)) mwa
= fmap (\(w,mwa) -> fmap (\(w',a) -> (w<>w', a)) mwa) >>> join
--      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- ここで、この関数に注目してみます。
-- この関数の型は (w, m (w, a)) -> m (w, a) です。
-- また、関数の中身がjoinWriterに似ていますが、
-- そのままではjoinWriterで置き換えられる部分がありません。
-- 
-- なのでまず (w, m (w, a)) の外側のWriterモナドとmを入れ替え、
-- fmap joinWriter :: m (w, (w, a)) -> m (w, a) と合成するとよさそうです。
= fmap (swapWM >>> fmap joinWriter) >>> join
= fmap swapWM >>> fmap (fmap joinWriter) >>> join
    where swapWM :: Functor m => (w, m b) -> m (w, b)
          swapWM (w, mb) = fmap (\b -> (w,b)) mb
```

めでたく、`WriterT`の`join`も単純な自然変換の合成で書けました。まとめると、

```haskell
-- Writerモナド (w, )のpureとjoin
pureWriter :: Monoid w => a -> (w, a)
pureWriter a = (mempty, a)

joinWriter :: Monoid w => (w, (w, a)) -> (w, a)
joinWriter (w, (w', a)) = (w <> w', a)

-- Writerとmの入れ替え
swapWM :: Functor m => (w, m b) -> m (w, b)
swapWM (w, mb) = fmap (\b -> (w,b)) mb

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  pure = pureWriter >>> pure >>> WriterT
  join = fmap runWriterT          -- WriterT w m (WriterT w m a) -> WriterT w m (m (w, a))
     >>> runWriterT               -- WriterT w m (m (w, a)) -> m (w, m (w, a))
     >>> fmap swapWM              -- m (w, m (w, a)) -> m (m (w, (w, a)))
     >>> fmap (fmap joinWriter)   -- m (m (w, (w, a))) -> m (m (w, a))
     >>> join                     -- m (m (w, a)) -> m (w, a)
     >>> WriterT                  -- m (w, a) -> WriterT w m a
```

これをストリング図に描いてみます。

![WriterTの定義](/images/string/writer-t.png)

![WriterTのpure](/images/string/writer-t-pure.png)

![WriterTのjoin](/images/string/writer-t-join.png)

青丸を`WriterT w m`のモナド演算（`pure`または`join`）に当てていて、
同様に緑丸を`Writer`モナド、赤丸をモナド`m`に対応させています。
また、二つの線が交わるところにある点が`swapWM`です。

![WriterTの構成要素](/images/string/writer-t-assumption.png)

さて、私達は`WriterT`を構成する2つのモナド`(w,_)`と`m`のモナド演算については
よくわかっていますが、自然変換`swapWM`についてはよくわかっていません。
そのため、ひとまず`WriterT`のモナド則の証明は後回しにしておきます。

### ReaderTの場合

`ReaderT`モナド変換子をストリング図に描く方法を考えます。

```haskell
newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

instance Functor m => Functor (ReaderT r m) where {- 省略 -}

-- WriterTはWriterモナドを部品として作ることができました。
-- ReaderTもそうなって欲しいですね。
pureReader :: a -> (r -> a)
pureReader = const
joinReader :: (r -> r -> a) -> (r -> a)
joinReader f r = f r r

instance (Monad m) => Monad (ReaderT r m) where
  pure = pure >>> pureReader >>> ReaderT
  join = fmap runReaderT >>> runReaderT >>> joinT >>> ReaderT
    where
      joinT :: (Monad m) => (r -> m (r -> m a)) -> r -> m a
      joinT rmrma = \r -> rmrma r >>= \rma -> rma r
```

ふたたび、`joinT`が単純な自然変換の合成になっていませんが、
`WriterT`のときと同じ作戦でいってみましょう。
`WriterT w m`が`Writer w = (w, )`と`m`の合成`Functor`だったように、
`ReaderT r m`も`m`と`Reader r = (r -> )`の合成`Functor`です。
そのため、`joinT`の引数は`Functor`の4段重ね`r -> m (r -> (m _))`になっています。
4段重ねの中央の2段、`m (r -> _)`を入れ替えられれば、`Reader`と`m`の`join`を使えます。

```haskell
-- mとReaderの入れ替え
swapMR :: (Functor m) => m (r -> b) -> r -> m b
swapMR mrb r = fmap ($ r) mrb

-- swapMRで中央を入れ替える方針で型を合わせるパズルをすれば、
-- joinTと同じ型の自然変換が見つかります。
joinT' :: (Monad m) => (r -> m (r -> m a)) -> r -> m a
joinT' = fmap swapMR >>> fmap (fmap join) >>> joinReader

-- joinT' = joinT を確認します。
joinT' rmrma
= joinReader $ fmap (fmap join) $ fmap swapMR rmrma
= joinReader $ fmap (fmap join) $ \r -> swapMR (rmrma r)
= joinReader $ fmap (fmap join) $ \r r' -> fmap ($ r') (rmrma r)
= joinReader $ \r r' -> join $ fmap ($ r') (rmrma r)
= \r -> join $ fmap ($ r) (rmrma r)
= \r -> rmrma r >>= ($ r)
= \r -> rmrma r >>= \rma -> rma r
= joinT rmrma
```

これをもとにストリング図を描くと、`WriterT`のものとラベル以外同じものが出来上がります。

![ReaderTの定義](/images/string/writer-t.png)

### ExceptTの場合

`ExceptT`も`ReaderT`や`WriterT`と"同じ構造"を持っています。
もはや細かい説明は不要かと思いますが、`ExceptT e m`はモナド`m`とモナド`Either e`の合成`Functor`で、
入れ替えをする自然変換`swapEM`によってモナドにしています。

```haskell
newtype ExceptT e m a =
  ExceptT { runExceptT :: m (Either e a) }

swapEM :: Monad m => Either e (m b) -> m (Either e b)
swapEM (Left e) = pure (Left e)
swapEM (Right mb) = fmap Right mb
```

### 3つをひとまとめにする

`WriterT`、`ReaderT`、`ExceptT`はどれも、
モナドの合成順を入れ替える自然変換を使って定義できました。
この3つのどれも、以下の構造を持っています。

* あるモナド`m`とモナド`n`の合成`m ∘ n`になっている
* 入れ替えをする自然変換`swap ::∀a. n (m a) -> m (n a)`を持っている
* `swap`を使って、`pure`と`join`が下図のように定義されている

  ![モナドの合成の一般形](/images/string/monad-compose.png)

|モナド変換子 |外側のモナド|内側のモナド|`swap`  |
|-------------|------------|------------|--------|
|`WriterT w m`| `m`        | `(w, )`    |`swapWM :: (w, m b) -> m (w, b)`   |
|`ReaderT r m`| `r -> `    | `m`        |`swapMR :: m (r -> b) -> r -> m b` |
|`ExceptT e m`| `m`        | `Either e` |`swapEM :: Either e (m b) -> m (Either e b)` |

## モナドの合成のモナド則

任意のモナドの組み合わせ`m, n`と前節の`swap`によって、
`m ∘ n`がモナドになると言いたいところですが、*どんな*自然変換でもよいのでしょうか？そんなことは無さそうです。

実際、どんな自然変換でも良いわけではありません。`WriterT`の構成にある`swapWM :: (w, m a) -> m (w, a)`で、
`Writer`部分の`w`を勝手に`mempty`に置き換えたりすれば、
出来上がった`WriterT w m`はモナド則を満たさなくなってしまいます。

しかし、「`swap`が特定の条件を満たせば`m ∘ n`がモナドになる」とは言えるはずです。
ストリング図を描いて、どんな条件を満たせばよいのか考えてみます。

まず、左単位法則から見てみます。

![]