---
title: 幅優先探索
---

# Haskellで幅優先探索

Haskellで[幅優先探索](https://ja.wikipedia.org/wiki/%E5%B9%85%E5%84%AA%E5%85%88%E6%8E%A2%E7%B4%A2)をしようとして、
キューをどうするか困ったことはないでしょうか？

まず思いつくだろうことは、[Data.Sequence.Seq](https://hackage.haskell.org/package/containers-0.6.3.1/docs/Data-Sequence.html#t:Seq)をキューとして使って、キュー`Seq node`を状態として持ち回れば、手続き型言語で普段書いていたような幅優先探索が書ける、ということでしょう。

もちろん、Mutableな配列をキューにしてもできます。`IO`や`ST`を探索以外に使わなければならない事情があればいい選択肢です。

しかし、キューを明示的に使わなくてもできる方法がいくつかあります。それぞれ面白みがあるので紹介していきます。

# 例題：コインで支払い

次の例題を考えます。

> この国では、金貨1枚は銀貨3枚に、プラチナ貨1枚は銀貨7枚に、ダイヤモンド貨1枚は銀貨19枚に相当します。銀貨100枚の価値がある商品を、なるべく少ない枚数の*銀貨以外の*コインで買う方法を見つけなさい。

（DPのほうが簡単というのは置いておいて、）この問題は、合計金額をノード、コイン1枚追加を辺とした有向非巡回グラフを考えて、合計金額100のノードまでのパスを幅優先探索で見つければいいですね。

この問題はHaskellで次のように書けます。

```haskell
type Coin  = Int
type Value = Int

type Graph label node = node -> [(label, node)]

addCoin :: Graph Coin Value
addCoin !n = [ (c,n+c) | c <- [3,7,19], n+c <= 100 ]
```

## キュー(ここでは`Seq`)を使う

```haskell
import Data.Foldable
import Data.Monoid (First(..))
import qualified Data.Sequence as S
import Data.Sequence (Seq(Empty, (:<|), (:|>)))

type Tree node = node -> [node]

bfSeq :: Tree node -> node -> [node]
bfSeq step root = loop (S.singleton root)
  where
    loop Empty     = []
    loop (n :<| q) = n : loop (foldl' (:|>) q (step n))

graphToPaths :: Graph label node -> Tree ([label], node)
graphToPaths graph (path, node)
  = [ (l : path, node') | (l, node') <- graph node ]

addCoin' :: Tree ([Coin], Value)
addCoin' = graphToPaths addCoin

firstJust :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
firstJust f = getFirst . foldMap (First . f)

addCoin' :: Tree ([Coin], Value)
addCoin' = graphToPaths addCoin

solvePuzzleSeq :: Maybe [Coin]
solvePuzzleSeq = firstJust f $ bfSeq addCoin' ([], 0)
  where f (path, 100) = Just (reverse path)
        f _           = Nothing
```

## 余再帰を使う

[元ネタ](https://kazu-yamamoto.hatenablog.jp/entry/20121107/1352259739)

```haskell
bfList :: Tree node -> node -> [node]
bfList step root =
    let ans = root : go 1 ans
     in ans
  where
    go n _ | n <= 0 = []
    go n (x:xs) = 
      let children = step x
      in children ++ go (n - 1 + length children) xs
    go _ [] = error "Never reach here"

solvePuzzleList :: Maybe [Coin]
solvePuzzleList = firstJust f $ bfList addCoin' ([], 0)
  where f (path, 100) = Just (reverse path)
        f _           = Nothing
```

`ans = root : go 1 ans`のように再帰的に構築されたリストが、
まるでキューのように扱えます。

## 遅延データ構造を使う

次の`Lazy`型を考えます。`Lazy a`は、`a`型の値が

* 計算できなかった ... `Fail`
* 計算終了した ... `Ok a`
* 計算中である ... `Next x`

という3つの状態を表します。`forceLazy`は、
これを単なる失敗または成功として`Maybe a`に単純化します。

```haskell
data Lazy a = Fail | Ok a | Next (Lazy a)
  deriving (Functor, Foldable, Traversable)

forceLazy :: Lazy a -> Maybe a
forceLazy Fail     = Nothing
forceLazy (Ok a)   = Just a
forceLazy (Next x) = forceLazy x
```

`Applicative`と`Monad`のインスタンスが次のように定義できます。

```haskell
instance Applicative Lazy where
  pure = Ok
  (<*>) = ap

instance Monad Lazy where
  return = pure
  Fail   >>= _ = Fail
  Ok a   >>= k = k a
  Next x >>= k = Next (x >>= k)
```

さらに、"2つの`Lazy a`のうち先に完了したほうを返す"を`(<|>)`として、
`Alternative`にもなります。

```haskell
instance Alternative Lazy where
  empty = Fail
  Fail   <|> y      = y
  Ok a   <|> _      = Ok a
  x      <|> Fail   = x
  _      <|> Ok a   = Ok a
  Next x <|> Next y = Next (x <|> y)
```

これを使って、BFSのようなものが実装できます。

```haskell
bfSearchLazy :: Tree node -> node -> (node -> Lazy a) -> Lazy a
bfSearchLazy step root goal = go root
  where
    go x = goal x <|> Next (asum $ fmap go (step x))

solvePuzzleLazy :: Maybe [Coin]
solvePuzzleLazy = forceLazy $ bfSearchLazy addCoin' ([], 0) f
  where f (path, 100) = Ok (reverse path)
        f _           = Fail
```

`bfSearchLazy`は、「木の全ノード`x`に対して、ルートからの距離に応じたステップ数後に`goal x`を評価する計算をさせ、一番先に完了した計算を採用する」と解釈できます。遅延評価のおかげで、これは幅優先探索と同じ深さまでしか木をたどりませんし、木が無限の深さであっても大丈夫です。
