---
title: reflectionを使ったテクニック
---

[reflection](http://hackage.haskell.org/package/reflection)というライブラリを使って、ちょっと便利なものを思いつきました。
[これです](https://gist.github.com/viercc/0f5e57d6c1cc1029eed2eb090d8f2a32)。

何をするものかと言うと、`forall a. Show a => Show (f a)`と書ける`Show`のインスタンスを持つ型`f`に対して、
`Show1 f`を機械的に定義できるようにするモジュールです。

``` haskell
-- | Automatic Show1(liftShowsPrec) 
autoLiftShowsPrec
  :: (Functor f)
  => (forall a. Show a => Int -> f a -> ShowS)
  -> (Int -> b -> ShowS)
  -> ([b] -> ShowS)
  -> Int -> f b -> ShowS

-- | Automatic Show1(liftShowList) 
autoLiftShowList
  :: (Functor f)
  =>  (forall a. Show a => [f a] -> ShowS)
  -> (Int -> b -> ShowS)
  -> ([b] -> ShowS)
  -> [f b] -> ShowS

data F a = ...
    deriving (Show, Functor)

instance Show1 F where
    liftShowsPrec = autoLiftShowsPrec showsPrec
    liftShowList = autoLiftShowList showList
```

Genericsが不要なことと、`reflection`以外のライブラリに依存しないことがウリです。
また、同じ手法で`Show2`,`Read1`, `Read2`もできます。残念ながら`(Eq|Ord)(1|2)`は無理です。

もしかしたらライブラリとしてすでに存在するのかもしれませんが、ちょっと探しきれなかったのでここで公開してみます。
要望があればちゃんとしたパッケージにします。
