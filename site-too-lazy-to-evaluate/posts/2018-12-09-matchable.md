---
title: matchable解説
---

最近、[matchable](http://hackage.haskell.org/package/matchable)というライブラリーを
Hackageに上げました。この記事では、matchableが何をするライブラリーなのか・なぜ作ったのかに
ついて解説します。

## matchableって何？

matchableは、その名の通り`Matchable`という型クラスを提供するライブラリーです。
その`Matchable`とは何かと言うと、[ドキュメント](http://hackage.haskell.org/package/matchable-0.1.1.1/docs/Data-Matchable.html#t:Matchable)をご覧ください。

では解説記事にならないので、解説します。といっても`Matchable`は大して複雑な型クラスではありません。
その定義であるソースコードを見たほうが早いでしょう。

``` haskell
class (Eq1 t, Functor t) => Matchable t where
  zipMatch :: t a -> t b -> Maybe (t (a,b))
  zipMatch = zipMatchWith (curry Just)

  zipMatchWith :: (a -> b -> Maybe c) -> t a -> t b -> Maybe (t c)
```

`Matchable t`における`t`は`Maybe`やリスト`[]`のようなコンテナです。
また、`Matchable`は、`zipMatch`と`zipMatchWith`という2つのメソッドを持つクラスです。それぞれ、次のような関数です。

* `zipMatch`は、2つのコンテナ`ta :: t a` と `tb :: t b`を取り、*もしこれらが全く同じ「かたち」をしていれば*、
対応する各要素をペアにした新しいコンテナ`tab :: t (a,b)`を返します。
ただし、`ta`と`tb`が全く同じ「かたち」でなければ、`zipMatch`は失敗します。

  成功/失敗は`Maybe`で表されます。成功すれば`Just tab`が、失敗すれば`Nothing`が返り値になるということです。
  
  具体例をあげると、リスト型`[]`の場合、`zipMatch`は
  次のような動作をします。
  
  * 2つの引数`ta`, `tb`の長さが同じなら、`Just (zip ta tb)`を返す
  * そうでなければ、`Nothing`を返す
  
  ```
  >>> zipMatch [1, 2, 3] ['a', 'b', 'c']
  Just [(1,'a'),(2,'b'),(3,'c')]
  >>> zipMatch [1, 2, 3] ['a', 'b']
  Nothing
  ```
  
  さて、『コンテナが全く同じ「かたち」をしていれば』という表現をさっき使いましたが、これでは少しあいまいです。
  なので、"Functor則"や"Monoid則"のように、`Matchable`のインスタンスが満たすべき"Matchable則"があります。

  __Matchable則__

  > `zipMatch ta tb = Just tab` が成立する ⇔  
  > 　　ある`tab`が存在して、`ta = fmap fst tab` かつ `tb = fmap snd tab`が成り立つ
  >
  >  さもなくば、`zipMatch ta tb = Nothing` である

* `zipMatch`に対する`zipMatchWith`は、`zip`に対する`zipWith`のようなものです。ただし、
  `zipMatchWith`が引数に取る関数は`a -> b -> Maybe c`です。この関数は、残り2つの引数として
  渡されたコンテナ`ta`, `tb`の対応する各要素に対して適用されますが、この関数が`Nothing`を
  返すと、`zipMatchWith`全体が`Nothing`を返します。
  
  実際、ドキュメントでは次の等式が成り立つことを要求しました。
  
  ```haskell
  zipMatchWith f ta tb = zipMatch ta tb >>= traverse (uncurry f)
  ```
  
  これまた例をリスト型`[]`で示すなら、次のようになります。
  
  ```
  >>> let f x y = if x >= y then Just (x - y) else Nothing
  >>> zipMatchWith f [1,2,3] [0,1,2]
  Just [1,1,1]
  >>> zipMatchWith f [1,2,3] [2,2,3]
  Nothing
  ```
  
  `zipMatchWith f [1,2,3] [2,2,3]`では、2つのリストは同じ長さですが、最初の要素で `f 1 2 = Nothing`
  なので全体としても`Nothing`になっています。
  
  省略しますが、`zipMatchWith`にも`zipMatch`と同じように満たすべき法則があります。

## なぜMatchableが必要なのか？

私が`Matchable`が必要だと感じたのは、自分で簡単なプログラミング言語を実装しているときでした。
パターンマッチングの実装を考え始め、次のようなコードを書き始めました。

``` haskell
data Value = IntVal Int
           | NullVal
           | ObjectVal ClassName [Value]

data Pattern = IntPat Int
             | NullPat
             | ObjectPat ClassName [Pattern]
             | VarPat VarName
```

そしてふと思ったのです。明らかに同じことを繰り返し書いている。どうにか簡潔に書けないかと。

``` haskell
data ValueF a = IntF Int
              | NullF
              | ObjectF ClassName [a]

type Value = Fix ValueF
type Pattern = Free ValueF VarName

patternMatch :: Pattern -> Value -> Maybe [(VarName, Value)]
patternMatch = {- 省略 -}
```

「これでイケルじゃん！」と思いました。次の関数を実装しようと考えるまでは。

``` haskell
-- | 一般化したパターンマッチ
patternMatch :: (???) => Free f a -> Fix f -> Maybe [(a, Fix f)]
patternMatch (Pure a) value         = Just [(a, value)]
patternMatch (Free fPat) (Fix fVal) =
  if 一番外側がマッチする fPat fVal
    then fmap fold . sequenceA $ zipWithみたいな関数 patternMatch fPat fVal
    else Nothing

一番外側がマッチする :: (Eq1 f) => f a -> f b -> Bool
一番外側がマッチする = liftEq (\_ _ -> True)
```

ここでつまづきました。いろいろなライブラリーを漁ってみても、既存の型クラスに

``` haskell
zipWithみたいな関数 :: (a -> b -> c) -> f a -> f b -> f c
```

を適切に実装できそうなものは思い当たりませんでした。
また、この`zipWithみたいな関数`は、前提条件として`一番外側がマッチする`が`True`である引数に対してしか定義できないという問題もありました。

そこで、「`zipMatch :: f a -> f b -> Maybe (f (a,b))`があったらいいなー」となったわけです。
その後、`zipMatch`の満たすべき性質についていろいろ考えた結果、この`Matchable`ができました。

## さらなる応用：ユニフィケーション

また、`Matchable`が既存のライブラリーに存在しないか調査する過程で、[unification-fd](http://hackage.haskell.org/package/unification-fd)というライブラリーを発見しました。そこにあったのは、

``` haskell
data UTerm t v = UVar !v
               | UTerm !(t (UTerm t v))

class Traversable t => Unifiable t where
    zipMatch :: t a -> t a -> Maybe (t (Either a (a, a))) 

unify :: (...ちょっと複雑な制約, 一部 Unifiable t を含む...)	 
      => UTerm t v	 
      -> UTerm t v	 
      -> em m (UTerm t v)

```

という非常によく似た型クラス`Unifiable`でした。これに触発されて、
`Matchable`を使ったユニフィケーションの例も[書いてみました](https://github.com/viercc/matchable/tree/master/example)。

## 実はいらない！？

実は、`zipMatch`は既存の型クラスの組み合わせで実装できたのです。

``` haskell
import Data.Functor.Classes (Eq1(..))
import Data.Foldable
import Control.Monad.State

zipMatch :: (Traversable f, Eq1 f) => f a -> f b -> Maybe (f (a,b))
zipMatch fa fb | liftEq (\_ _ -> True) fa fb = Just (unsafeZip fa fb)
               | otherwise                   = Nothing

unsafeZip :: (Traversable f) => f a -> f b -> f (a,b)
unsafeZip fa fb = evalState (traverse step fa) (toList fb)
  where
    step :: a -> State [b] (a,b)
    step a = state $ \bs ->
      [] -> error "differently shaped arguments"
      (b:bs) -> ((a,b),bs)
```

しかし、この実装は（難癖に近いかもしれませんが）少しだけ問題があります。

1. `Eq1`には法則が無いため、本当に安全に`unsafeZip`が呼び出せる保証がないこと。
   `Matchable`は新しい型クラスなので、必要なMatchable則を定義できる。
2. `liftEq`と`traverse`と`toList`で、`fa`と`fb`をそれぞれ2回走査しなければいけないこと。
   ほとんどの場合`zipMatch`は1回の走査で実装できる。

このうち2.はあまり関係ない(`Matchable`のインスタンスは大抵非再帰的な小さい型)のですが、
1.は`Matchable`をライブラリーとして公開する理由になると考えています。

## 結論

`Matchable`という型クラスを提供するmatchableライブラリーを作ったので、紹介しました。
`Matchable`はパターンマッチやユニフィケーションを実装するのに便利です。
