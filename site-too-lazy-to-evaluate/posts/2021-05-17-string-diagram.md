---
title: ストリング図でMonad再入門(1)
published: 2021-05-17
---

## いまさらモナド

この記事はHaskellにおけるモナドの解説です。
そして、「またかよ」「もう知ってる」と思われた方が想定読者です。

（ほんとうにモナドについて初めて理解したくて来た方は申し訳ありません。
一応アドバイスするなら、私は[Haskell Wiki](https://wiki.haskell.org/Haskell)等のWeb上の資料と
[すごいHaskell](https://www.ohmsha.co.jp/book/9784274068850/)
で学びました。基礎を抑える感じの良い本と思いましたが、
合わなかったという感想もよく聞きます。）

ねらいとしては、
[ストリング図](https://en.wikipedia.org/wiki/String_diagram)という表記法を使って、
モナドについての（おそらくすでに知っているでしょう）計算が
とても視覚的にできるようになって**楽しい**ということの紹介です。

以下の文献・Webページを参考にしました。

* [String diagram - Wikipedia](https://en.wikipedia.org/wiki/String_diagram)
  * ざっくりした概要
  * Wikipedia日本語版にはなかった（残念）
* [絵算の威力をお見せしよう - 檜山正幸のキマイラ飼育記 (はてなBlog)](https://m-hiyama.hatenablog.com/entry/20180302/1519974841)
  * 日本語、すごく勉強になるブログ
  * リンク先記事が最もまとまっていると感じましたが、それ以外にもたくさん参考にしました。
* [Composing Monads, Mark P. Jones and Luc Duponcheel, Research Report YALEU/DCS/RR-1004, 1993](http://web.cecs.pdx.edu/~mpj/pubs/composing.html)
  * Monad transformersの原点的なもの
* 他たくさんあると思いますが、覚えてなくてリストアップできませんごめんなさい・・・

## ストリング図

[ストリング図](https://en.wikipedia.org/wiki/String_diagram)は、
圏論で使われる表記法です。圏論から道具を拝借するときによくあることですが、
ストリング図は"2-圏における2-射"という抽象度の高いものを描くよう定義されています。
しかし、今回の記事の中では、`Monad`について考えるだけなので、抽象度を下げたもの
を説明していきます。

ストリング図が表すものは、`Functor`の間の自然変換です。
改めて明示的に定義するなら、
`Functor f`と`Functor g`に対して、型`∀a. f a -> g a`が付くような関数が、`f`から`g`への自然変換です。

自然変換`tf :: ∀a. f a -> f' a`を、以下の図のように描くことにします。

![ストリング図](/images/string/1.png) 

図の中で、それぞれの線はある`Functor`に、線を結ぶ丸が自然変換`tf`に対応しています。

"何もしない"自然変換`id :: ∀a. f a -> f a`は、ただの線で描きます。

![ストリング図(id)](/images/string/id.png)

加えて、`∀a. f (g a) -> h a`のように`Functor`がネストしているような場合も、
`f (g a)`と`Compose f g a`を同一視して、"`Compose f g`から`h`への自然変換"とみなすことにします。
何段ネストしていてもこれは変わらないことにしましょう。

このようなネストした`Functor`間の自然変換は、以下の図のように描くことにします。

![ストリング図(合成Functor1)](/images/string/2.png) 

![ストリング図(合成Functor2)](/images/string/3.png)

上に突き出している端がそれぞれ`h, g, f`なのは、この自然変換が`Functor`の合成`f ∘ g ∘ h`を入力にとることを表していて、
下に突き出している端が`q, p`なのは、`p ∘ q`を出力することを表しています。
合成が*逆順*なのに注意してください。

さらに、"0個の`Functor`のネスト"をも、`Identity`と同一視します。
つまり、`pure :: ∀a. a -> f a`も`Identity`から`f`への自然変換とみなして、次の図のように書くことにします。このとき、図でうすく描いたような、`Identity`を表す線は引かないことにします。
（これによって後で困ることはありません！）

![ストリング図(Identityの省略)](/images/string/pure-and-extract.png)

自然変換どうしは垂直合成する（"縦につなげる"）こともできました。上図の`nt`と`foo`は、
合成して自然変換`nt >>> foo :: ∀a. f (g (h a)) -> p a`を作ることができます。
このように合成した自然変換は、
図を縦につなげて以下のように表します。
（ここでは、`foo . nt`のように`.`を使わず、代わりに`>>>`で関数の合成を表記することにします。）

![ストリング図の垂直合成](/images/string/vcomp.png)

自然変換どうしを水平に合成する（"横にならべる"）こともできます。
ふたつの自然変換`tf :: ∀a. f a -> f' a` と `tg :: ∀a. g a -> g' a`があるとき、`tfg :: ∀a. f (g a) -> f' (g' a)`
が次のように定義できます。

```haskell
tfg :: ∀ a. f (g a) -> f' (g' a)
tfg = fmap tg >>> tf
    = tf >>> fmap tg
  -- どちらも等しい
```

![ストリング図の水平合成](/images/string/hcomp.png)

とくに、`id`と水平合成する場合が頻出です。

![ストリング図の水平合成（idと）](/images/string/hcomp-id.png)

例を挙げてみましょう。次のように、`catMaybes`を
`maybeToList`と`concat`で表したとします。

```haskell
catMaybes :: [Maybe a] -> [a]
catMaybes = fmap maybeToList >>> concat

concat :: [[a]] -> [a]
maybeToList :: Maybe a -> [a]
```

`catMaybes, maybeToList, concat`のいずれも、（ネストを許した広い意味で）自然変換です。
`catMaybes`の右辺をストリング図で描いてみると次のようになります。
`Maybe`と`[]`の合成順（左から右、Haskellでの記述と*逆順*）に気をつけてください。

![ストリング図の例(catMaybes)](/images/string/catmaybes.png)

## ストリング図でMonad

`Monad`の定義を決めておきます。
ここでは、現実にHaskellで使われている定義ではないですが、
同値な定義として次のクラスを`Monad`だとします。

```haskell
-- | Monadのインスタンスは以下のモナド則を満たさなければならない。
--
-- [単位法則]
--
--     > pure >>> join = fmap pure >>> join = id
--     普段どおり(.)を使って書くならば、
--     > join . pure   = join . fmap pure   = id
--
-- [結合法則]
--
--     > join >>> join = fmap join >>> join
--     普段どおり(.)を使って書くならば、
--     > join . join = join . fmap join
class (Functor m) => Monad m where
  pure :: a -> m a
  join :: m (m a) -> m a

return :: Monad m => a -> m a
return = pure

(>>=) :: Monad m => m a -> (a -> m b) -> m b
ma >>= f = join (fmap f ma)
```

`pure`、`join`ともに自然変換であり、モナド則も含めて
ストリング図で描くことができます。
これにより、文字で書かれた「`Functor`である`m`が`Monad`である」という条件が、
次のように図で描けてしまいます。

* 以下の自然変換`pure`と`join`があること：

  ![pureとjoin](/images/string/monad-pure-join.png)

* 加えて、以下のストリング図の等式が成り立つこと：

  ![単位法則](/images/string/monad-law-unit.png)

  ![結合法則](/images/string/monad-law-assoc.png)

## ストリング図で`State`モナド

次の`State`モナドがモナド則を満たしていることを証明してみましょう。

```haskell
newtype State s a = State { runState :: s -> (s, a) }

instance Functor (State s) where {- 省略 -}

instance Monad (State s) where
  pure a = State (\s -> (s, a))
  join mma = State $ \s ->
    let (s', ma) = runState mma s
    in runState ma s
```

ここで、`State`が二つの`Functor`の合成からなっていることに注目して、
次のように書き換えてみます。

```haskell
type G s = (->) s -- (s ->) と書きたいが、Haskellはこの書き方は不可
type F s = (,) s  -- (s, )  〃

-- G s = (s ->)も、 F s = (s, )も、Functorのインスタンス

newtype State s a = State { runState :: G s (F s a) }
  -- State s a ~ Compose (G s) (F s) a

instance Monad (State s) where
  pure = open >>> State
  join =   runState              -- :: State s (State s a) -> G s (F s (State s a))
       >>> fmap (fmap runState)  -- :: G s (F s (State s a)) -> G s (F s (G s (F s a)))
       >>> fmap close            -- :: G s (F s (G s (F s a))) -> G s (F s a)
       >>> State                 -- :: G s (F s a) -> State s a

open :: a -> G s (F s a)   -- a -> (s -> (s, a))
open a = \s -> (s, a)

close :: F s (G s a) -> a  -- (s, s -> a) -> a
close (s, f) = f s
```

`open`と`close`という命名は、これらが対になっているところからきています。

```haskell
open >>> fmap close = id :: G s a -> G s a
(open >>> fmap close) (f :: G s a)   -- G s a = (s -> a)
  = fmap close $ \s -> (s, f)
  = \s -> close (s, f)
  = \s -> f s
  = f

fmap open >>> close = id :: F s a -> F s a
(fmap open >>> close) ((s, a) :: F s a)  -- F s a = (s, a)
  = close $ (s, open a)
  = close $ (s, \s -> (s, a))
  = (\s -> (s, a)) s
  = (s, a)
```

`open, close`と、`State`の`newtype`をつけたり外したりする`State, runState`はいずれも自然変換
になっており、以下の通りストリング図に描けます。

![Stateモナドの構成要素](/images/string/state-elements.png)

そして、`open`と`close`の間に成り立つ関係は次の図のように描けます。

![openとcloseの関係](/images/string/state-openclose.png)

"曲がった線"をまっすぐに伸ばすことができるという、見た目にわかりやすい関係になっているところがポイントです。

<div class='sidenote'>
より一般的な話としては、`open, close`のペアは`F s`が`G s`の[左随伴](https://ja.wikipedia.org/wiki/随伴関手)であるという
ことを表します。`open, close`は私が勝手に使った用語法で、普通は単位(unit)、余単位(counit)と呼び、
ギリシャ文字`η, ε`で表します。

`open`と`close`の関係は、上図にあるストリング図の見た目から、ジグザグ関係式などと呼ばれています。
</div>

ここまでの道具を使えば、`State`のモナド則は図を描いていくだけで証明できます。
まず、`pure`と`join`をストリング図で書きます。

![Stateのpureとjoin](/images/string/state-pure-join.png)

モナド則は、ストリング図の等式をつかって変形していくことで証明できます。

![Stateのモナド則(左単位法則のみ。右単位法則も左右が入れ替わるだけで同様)](/images/string/state-left-unit.png)

![Stateのモナド則(結合法則)](/images/string/state-assoc.png)
