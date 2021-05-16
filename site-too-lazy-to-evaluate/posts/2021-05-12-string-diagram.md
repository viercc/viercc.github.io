---
title: ストリング図でMonad再入門
---

## いまさらモナドの解説を

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
  * 簡潔にまとまった定義など
  * Wikipedia日本語版にはなかった（残念）
* [絵算の威力をお見せしよう - 檜山正幸のキマイラ飼育記 (はてなBlog)](https://m-hiyama.hatenablog.com/entry/20180302/1519974841)
  * 日本語、すごく勉強になるブログ
* [Composing Monads, Mark P. Jones and Luc Duponcheel, Research Report YALEU/DCS/RR-1004, 2013](http://web.cecs.pdx.edu/~mpj/pubs/composing.html)
  * Monad transformersの原点的なもの

### ストリング図

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

![ストリング図(Identityの省略)](/images/string/pure.png)

自然変換どうしは垂直合成する（"縦につなげる"）こともできました。上図の`nt`と`foo`は、
合成して自然変換`nt >>> foo :: ∀a. f (g (h a)) -> p a`を作ることができるます。
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
