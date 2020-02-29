---
title: 可換なモナドとは？細かい計算部分
---

（直前の投稿の付録です。）

単位律は簡単なので結合律だけゴリゴリ計算します。

```haskell
x = ListT mta :: ListT m a
f :: a -> ListT m b
g :: b -> ListT m c

x >>= f
  = ListT mta >>= f
  = ListT $ fmap concat $ mta >>= traverse (runListT . f)
(x >>= f) >>= g
  = ListT $ fmap concat $
     (fmap concat $ mta >>= traverse (runListT . f)) >>=
     traverse (runListT . g)
   -- fmap f mx >>= k  =  mx >>= (k . f)
  = ListT $ fmap concat $
    (mta >>= traverse (runListT . f)) >>=
    (traverse (runListT . g) . concat)
   -- 補題(traverse-concat)
  = ListT $ fmap concat $
    (mta >>= traverse (runListT . f)) >>=
    (fmap concat . traverse (traverse (runListT . g)))
   -- fmapを移動
  = ListT $ fmap concat $ fmap concat $
    (mta >>= traverse (runListT . f)) >>=
    traverse (traverse (runListT . g))
   -- fmapを融合
   -- Monad m の結合法則
  = ListT $ fmap (concat . concat) $
    mta >>= \ta -> traverse (runListT . f) ta >>= traverse (traverse (runListT . g))
   -- join と fmap を使って                     ^ ここの>>=を書き換える
  = ListT $ fmap (concat . concat) $
    mta >>= \ta ->
      join . fmap (traverse (traverse (runListT . g))) . traverse (runListT . f) $ ta
   -- eta-reduction
   -- Traversable則, composition
  = ListT $ fmap (concat . concat) $
    mta >>=
      join . runCompose . traverse (Compose . fmap (traverse (runListT . g)) . runListT . f)
   -- join . runCompose = join'
   -- Traversable則, naturality
  = ListT $ fmap (concat . concat) $
    mta >>=
      traverse (join' . Compose . fmap (traverse (runListT . g)) . runListT . f)
   -- join' . Compose = join . runCompose . Compose = join
   -- join . fmap g . f = (f >=> g)
  = ListT $ fmap (concat . concat) $
    mta >>=
      traverse (runListT . f >=> traverse (runListT . g)))
   -- concat = リストモナド[]のjoin なので、結合律が成り立っていて、
   --   concat . concat = concat . fmap concat
  = ListT $ fmap concat $ fmap (fmap concat) $
    mta >>=
      traverse (runListT . f >=> traverse (runListT . g)))
  = ListT $ fmap concat $
    mta >>=
      fmap (fmap concat) . traverse (runListT . f >=> traverse (runListT . g))
   -- fmap (fmap h) . traverse f
   --   = fmap (fmap h) . sequenceA . fmap f
   --   = sequenceA . fmap (fmap h) . fmap f
   --   = traverse (fmap h . f)
  = ListT $ fmap concat $
    mta >>=
      traverse (fmap concat . (runListT . f >=> traverse (runListT . g)))
  = ListT $ fmap concat $
    mta >>=
      traverse (\a -> fmap concat $ runListT (f a) >>= traverse (runListT . g))
   -- ListTの(>>=)の定義と、外側のtraverseの中の関数を比べると、次がわかる
  = ListT $ fmap concat $
    mta >>=
      traverse (runListT . (\a -> f a >>= g)
  = ListT mta >>= (\a -> f a >>= g)
  = x >>= (\a -> f a >>= g)
```

計算中に、次の補題(traverse-concat)を使いました。

```haskell
-- fを任意のApplicative, h :: a -> f b, tta :: [[a]] とする。
-- 以下の式が成り立つ。
traverse h (concat tta) = fmap concat $ traverse (traverse h) tta

-- まず次の事実を示しておく。
traverse h (x ++ y) = (++) <$> traverse h x <*> traverse h y
  -- xに関する帰納法。
  -- x = []のとき
  traverse h ([] ++ y) = traverse h y
  (++) <$> traverse h [] <*> traverse h y
    = (++) <$> pure [] <*> traverse h y
    = traverse h y
  
  -- x = a:x' のとき
  traverse h ((a : x') ++ y)
    = traverse h (a : x' ++ y)
    = (:) <$> h a <*> traverse h (x' ++ y)
  (++) <$> traverse h (a : x') <*> traverse h y
    = (++) <$> ((:) <$> h a <*> traverse h x') <*> traverse h y
    = (\b xb yb -> (b : xb) ++ yb) <$> h a <*> traverse h x' <*> traverse h y
    = (\b xb yb -> b : (xb ++ yb)) <$> h a <*> traverse h x' <*> traverse h y
      -- Applicative則でごちゃごちゃやる
    = (:) <$> h a <*> ((++) <$> traverse h x' <*> traverse h y)
      -- 帰納法の仮定
    = (:) <$> h a <*> traverse h (x' ++ y)

-- 証明。 ttaに関する帰納法
  -- tta = [] のとき
  traverse h (concat []) = traverse h [] = pure []
  fmap concat $ traverse (traverse h) [] = fmap concat $ pure [] = pure []

  -- tta = ta : tta' のとき
  traverse h (concat (ta : tta'))
    = traverse h (ta ++ concat tta')
    = (++) <$> traverse h ta <*> traverse h (concat tta')
  fmap concat $ traverse (traverse h) (ta : tta')
    = fmap concat $ (:) <$> traverse h ta <*> traverse (traverse h) tta'
    = (\tb ttb -> concat (tb : ttb)) <$> traverse h ta <*> traverse (traverse h) tta'
    = (\tb ttb -> tb ++ concat ttb) <$> traverse h ta <*> traverse (traverse h) tta'
    = (++) <$> traverse h ta <*> fmap concat (traverse (traverse h) tta')
      -- 帰納法の仮定
    = (++) <$> traverse h ta <*> traverse h (concat tta')
```
