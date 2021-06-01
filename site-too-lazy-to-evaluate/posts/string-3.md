---
title: ストリング図でMonad再入門(3)
published: 2021-06-01
---

[前回](2021-05-24-string-2.html)、ストリング図を使って`StateT`モナド変換子のモナド則を証明しました。
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
      pureWriter a = (mempty, a) -- Writerモナド (w,_) のpure
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
-- Writerモナド(w,_)のjoinが使えそうです
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
`ReaderT r m`も`m`と`Reader r = (r -> _)`の合成`Functor`です。
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

![ReaderTの定義](/images/string/reader-t-all.png)

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
|`WriterT w m`| `m`        | `(w,_)`    |`swapWM :: (w, m b) -> m (w, b)`   |
|`ReaderT r m`| `r -> _`   | `m`        |`swapMR :: m (r -> b) -> r -> m b` |
|`ExceptT e m`| `m`        | `Either e` |`swapEM :: Either e (m b) -> m (Either e b)` |

## モナドの合成のモナド則

任意のモナドの組み合わせ`m, n`と前節の`swap`によって、
`m ∘ n`がモナドになると言いたいところですが、*どんな*自然変換でもよいのでしょうか？そんなことは無さそうです。

実際、なんでもOKではありません。`WriterT`の構成にある`swapWM :: (w, m a) -> m (w, a)`で、
モノイド`w`を勝手に`mempty`に置き換えたりすれば、
出来上がった`WriterT w m`はモナド則を満たさなくなってしまいます。

しかし、「`swap`が特定の条件を満たせば`m ∘ n`がモナドになる」とは言えるはずです。
ストリング図を描いて、どんな条件を満たせばよいのか考えてみます。

まず、左単位法則から見てみます。

![モナドの合成、左単位法則](/images/string/monad-compose-left-unit.png)

ピンク色で強調した部分が*成り立っているかどうかわからない*等式で、
それ以外の部分は`m`,`n`のモナド則といった、すでに知っている等式です。
この*成り立ってほしい等式(1)*は、もっと単純なバージョン（下図右辺）と同値になります。

![成り立ってほしい等式(1)](/images/string/swap-left-unit.png)

右単位法則が成り立つ条件から、同様に次の*成り立ってほしい等式(2)*が出てきます。

![成り立ってほしい等式(2)](/images/string/swap-right-unit.png)

最後に結合法則を見てみます。（結合法則が成り立つために成り立ってほしい等式を、
ピンク色で強調しています。）

![モナドの合成、結合法則](/images/string/monad-compose-assoc.png)

成り立ってほしい等式だけ取り出せば、次のようになります。

![成り立ってほしい等式(3)(4)](/images/string/swap-dist.png)

これらの等式(1)-(4)を満たすような`swap`であれば、`m ∘ n`がモナドになると言えます。
等式(1)-(4)を、ストリング図からHaskellの式に書き直すと、次のようになります。

```haskell
instance Monad m
instance Monad n

swap :: ∀b. n (m b) -> m (n b)

-- 等式(1)
pure >>> swap = fmap pure :: ∀b. m b -> m (n b)
-- 等式(2)
fmap pure >>> swap = pure :: ∀b. n b -> m (n b)
-- 等式(3)
join >>> swap :: ∀b. n (n (m b)) -> m (n b)
  = fmap swap >>> swap >>> fmap join
-- 等式(4)
fmap join >>> swap :: ∀b. n (m (m b)) -> m (n b)
  = swap >>> fmap swap >>> join
```

自然変換`swap`によって(1)-(4)が成り立つことを、
「`swap`は、モナド`m`がモナド`n`に対する[^1]分配である[^2]」と呼ぶことにして、
ここで証明できたことをまとめると、次のようになります。

> モナド`m`がモナド`n`に対する分配`swap`を持てば、`swap`を使って`m ∘ n`がモナドになる

これを`WriterT`の場合に適用すれば、`WriterT w m`がモナド則を満たしていることの証明は、
`swap=swapWM`が分配であることを確認すればOKです。

```haskell
-- 再掲
swapWM :: Functor m => (w, m b) -> m (w, b)
swapWM (w, mb) = fmap (\b -> (w,b)) mb

-- 等式(1)
pureWriter >>> swapWM = fmap pureWriter :: ∀b. m b -> m (w, b)
(pureWriter >>> swapWM) mb
 = swapWM (mempty, mb)
 = fmap (\b -> (mempty, b)) mb
 = fmap pureWriter mb
-- 等式(2)
fmap pure >>> swapWM = pure :: ∀b. (w, b) -> m (w, b)
fmap pure >>> swapWM $ (w,b)
 = swapWM (w, pure b)
 = fmap (\b -> (w,b)) (pure b)
 = pure (w,b)
-- 等式(3)
joinWriter >>> swapWM :: ∀b. (w, (w, m b)) -> m (w, b)
  = fmap swapWM >>> swapWM >>> fmap joinWriter
joinWriter >>> swapWM $ (w,(w',mb))
  = swapWM (w <> w', mb)
  = fmap (\b -> (w <> w', b)) mb
fmap swapWM >>> swapWM >>> fmap joinWriter $ (w,(w',mb))
  = swapWM >>> fmap joinWriter $ (w, swapWM (w', mb))
  = fmap joinWriter $ swapWM (w, swapWM (w', mb))
  = fmap joinWriter $ fmap (\b -> (w,b)) $ fmap (\b -> (w',b)) mb
  = fmap (joinWriter . (\b -> (w,b)) . (\b -> (w',b))) $ mb
  = fmap (\b -> joinWriter (w,(w',b))) mb
  = fmap (\b -> (w <> w', b)) mb
-- 等式(4)
fmap join >>> swapWM :: ∀b. (w, m (m b)) -> m (w, b)
  = swapWM >>> fmap swapWM >>> join
fmap join >>> swapWM $ (w, mmb)
  = swapWM (w, join mmb)
  = fmap (\b -> (w,b)) $ join mmb
swapWM >>> fmap swapWM >>> join $ (w, mmb)
  = fmap swapWM >>> join $ fmap (\mb -> (w,mb)) mmb
  = join $ fmap (swapWM . (\mb -> (w,mb))) mmb
  = join $ fmap (\mb -> swapWM (w,mb)) mmb
  = join $ fmap (\mb -> fmap (\b -> (w,b)) mb) mmb
  = join $ fmap (fmap (\b -> (w,b))) mmb
    -- join . fmap (fmap f) = fmap f . join
  = fmap (\b -> (w,b)) $ join mmb
```

`ReaderT`も`ExceptT`も、同じように`swapMR`、`swapEM`が分配であることが示せて、
モナド則を満たすことがわかります。

[^1]: （注意）

    「モナド`m`がモナド`n`に対する……」において、
    `m`と`n`の順番には意味があります。
    `swap :: ∀b. n (m b) -> m (n b)`があるからといって、逆向きの自然変換
    `reverseSwap :: ∀b. m (n b) -> n (m b)`があったり、
    それが等式(1)-(4)を満たす保証はまったく無いからです。

    そのため、「モナド`m,n`の……」のように並列で呼ばないようにしました。

[^2]: 「分配」という単語は、これが圏論では「分配律(distributive law)」と呼ばれていることから取っています。

    「分配律」から「律」を落としたのは、モナド則の結合法則などの自然変換の間の等式と混同しないためです。
    等式(1)-(4)を満たすような`swap`それ自体が「分配律」と呼ばれていて、等式(1)-(4)は「分配律」
    の満たすべき性質（言うなれば「分配律律」）です。
    
    ややこしすぎて本文に書くことでは無いと思いました。
