---
title: ストリング図でMonad再入門(2)
---

## ストリング図で`WriterT`

つづいて、`WriterT`がモナド則を満たしていることを証明してみましょう。

もう少し明確にするなら、任意のモノイド`w`とモナド`m`とに対して、
次の`WriterT w m`がモナド則を満たすことを、ストリング図を使って証明してみます。

```haskell
-- transformers パッケージのものとは少し違います
newtype WriterT w m a = WriterT { runWriterT :: m (w, a) }

instance Functor m => Functor (WriterT w m) where {- 省略 -}

instance (Monoid w, Monad m) => Monad (WriterT w m) where
  pure = pureT >>> WriterT
    where
      -- ScopedTypeVariables
      pureT :: ∀a. a -> m (w, a)
      pureT a = pure (mempty, a)
  join = runWriterT >>> fmap runWriterT >>> joinT >>> WriterT
    where
      -- ScopedTypeVariables
      joinT :: ∀a. m (w, m (w, a)) -> m (w, a)
      joinT mwmw =
        do (w, mw) <- mwmw
           (w', a) <- mw
           return (w <> w', a)
```

ストリング図をつかった計算に入るために、自然変換の組み合わせで`pureT`と`joinT`を書いてみます。
そのためにまず、`(,) w`がモナドになることを利用します。

```haskell
instance Functor ((,) w) where {- 省略 -}

instance (Monoid w) => Monad ((,) w) where
  pure :: a -> (w, a)
  pure a = (mempty, a)

  join :: (w, (w, a)) -> (w, a)
  join (w, (w', a)) = (w <> w', a)

-- この定義でたしかにモナド則を満たしているが、証明は省略する。
```

このモナドを使って`pureT, joinT`を書き換えてみます。

```haskell
pureT :: ∀a. a -> m (w, a)
pureT a = pure (mempty, a)
pureT = pure >>> pure
--      ^        ^
--      |        \-- ∀a. a -> m a
--      \-- ∀a. a -> (w, a)

joinT :: ∀a. a -> m (w, m (w, a)) -> m (w, a)
joinT mwmw =
  do (w, mw) <- mwmw
     (w', a) <- mw
     return (w <> w', a)
= do (w, mw) <- mwmw
     (w', a) <- mw
     return (join (w, (w', a))) -- ((,) w) の join
= do (w, mw) <- mwmw
     fmap (\w'a -> join (w, w'a)) mw
= do (w, mw) <- mwmw
     fmap ((,) w >>> join) mw
= join $ fmap (\(w, mw) -> fmap ((,) w >>> join) mw) mwmw
-- ^ m の join

joinT
 = fmap (\(w, mw) -> fmap ((,) w >>> join) mw) >>> join
 = fmap (\(w, mw) -> fmap ((,) w) mw) >>> fmap (fmap join) >>> join
--      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--      | この関数に名前をつける
 = fmap swap_wm >>> fmap (fmap join) >>> join
 where
   swap_wm :: ∀b. (w, m b) -> m (w, b)
   swap_wm (w, mb) = fmap ((,) w) mb
```
