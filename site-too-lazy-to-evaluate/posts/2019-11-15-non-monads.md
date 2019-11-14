---
title: モナドになれないFunctor
---

## モナドになれないFunctor (A Functor which can't be a Monad)

このFunctorをMonadにする方法があるだろうか、という問題を考えます。

    data F2 x = Z | P x x
      deriving (Functor)

    pure :: forall x. x -> F2 x
    join :: forall x. F2 (F2 x) -> F2 x

`pure x ≠ Z` であることは簡単にわかります。`join . pure = id` でなければなりませんが、
`pure x = Z` であればその等式が成り立ちません。

    pure x = P x x   -- (1)

`join`についてはどうでしょうか？ 自明にわかることとして、次の式が成り立つ必要があります。

    join Z = Z           -- (2)

コンストラクタ `P` に渡すための値がないため、右辺は `Z` 一択になります。

モナド則を見れば、さらに`join`の実装を絞り込むことができます。

    -- join . pure = id
    join (P mx mx) = mx
    join (P Z Z) = Z
    join (P (P x y) (P x y)) = P x y      -- (4)

    -- join . fmap pure = id
    join $ fmap pure (P x y)
      = join (P (P x x) (P y y)) = P x y  -- (5)

\(4) と (5) を同時に満たすような実装は次のものしかありません。

    join (P (P x y) (P z w)) = P x w      -- (6)

モナド則最後の一つは、次の等式で書かれる結合則です。

    join . join = join (fmap join)

さて、いくつかのパターンで`join`が返すべき値が決まってしまっていますが、
次のパターンでは何を返せばいいでしょうか？実は、何を返してもモナド則に
従うことができないのです！

    join (P (P x y) Z) = ???

`??? = Z` の場合、結合則の反例を次のように構成できます。

    bad1 = P (P (P x y) Z      )
             (P Z       (P z w))

    (join . join)      bad1 = join (P (P x y) (P z w)) = P x w
    (join . fmap join) bad1 = join (P Z (join (P Z (P z w)))) ≠ P x w

一方は`x`に依存した値を返すのに対し、もう一方は`x`に依存しないので、これらは一致しません。

`??? = P (x または y) (x または y)` の場合。複雑になるので、どの組み合わせでも成立する
`join (P (P x x) Z) = P x x`を仮定して、結合則の反例を構成します。

    bad2 = P (P (P x x) Z)
             (P (P y y) Z)

    (join . join) bad2
      = join $ P (P x x) Z
      = P x x
    (join . fmap join) bad2
      = join $ P (P x x) (P y y)
      = P x y
      ≠ P x x

結果として、`F2`にモナド則を満たすインスタンスを与えることはできないことがわかります。

## 一般化しよう

もっと一般に、

    data F k x = Zero | Pow (k -> x)
        deriving (Functor)

という形のFunctorでも同じことが証明できます。
`F2`は`F Bool`とだいたい同型なので、これは一般化になっています。
また、`F k`は`Compose Maybe ((->) k)`とも同型なので、`Applicative`でもあります。

`F2`の場合と同じ議論によって、

    pure :: forall x. x -> F k 
    pure x = Pow (const x)

および

    join :: forall x. F k (F k x) -> F k x
    join Zero = Zero
    join (Pow $ \_ -> Zero) = Zero
    join $ Pow (\i -> Pow (\j -> f i j)) = Pow (\i -> f i i)  -- (join-Pow-Pow)

が成り立ちます。

いま、型`k`に少なくとも2つの異なる値が属していて、これらを識別する関数`p`があるとします。

    -- p truthy = True
    -- p falsy = False
    p :: k -> Bool
    truthy, falsy :: k

この`p`を使って、次の関数を定義します。

    ifP, unlessP :: forall x. x -> F k (F k x)
    ifP x = Pow (\i -> if p i then pure x else Zero)
    unlessP x = Pow (\i -> if p i then Zero else pure x)

`F2`の場合と同じように、次の場合に`join`が何を返すべきかを考えます。

    join (ifP x) = ???

`join (ifP x) = Zero` と仮定すると…

    type A :: *
    x, y :: A
    
    bad1 :: F k (F k (F k A))
    bad1 = Pow (\i -> if p i then ifP x else unlessP y)
           -- Notice that both `ifP` and `unlessP` returns `Pow _`
         = Pow $ \i -> Pow $ \j ->
             if p i
               then if p j then pure x else Zero
               else if p j then Zero   else pure y

    (join . join) bad1
         -- Use (join-Pow-Pow)
       = join $ Pow $ \i ->
           if p i
             then if p i then pure x else Zero
             else if p i then Zero   else pure y
       = join $ Pow \i -> if p i then pure x else pure y
       = join $ Pow \i -> Pow $ if p i then const x else const y
       = Pow $ \i -> if p i then x else y

    (join . fmap join) bad1
         -- Use definition of fmap
       = join $ Pow $ \i -> if p i then join (ifP x) else join (unlessP y)
         -- Use the assumption: join (ifP x) = Zero
       = join $ Pow $ \i -> if p i then Zero else join (unlessP y)

今、`(join . join) bad1` は`x`に依存しますが、`(join . fmap join) bad1`は依存しません。そのため、これらは一致しません。

逆に、`join (ifP x) = Pow f`と仮定します。このとき、`f :: k -> x` が返すことができる値は`x`以外にないので、どんな実装がされているかに関係なく `join (ifP x) = Pow (const x) = pure x`です。

    bad2 :: F k (F k (F k A))
    bad2 = Pow (\i -> if p i then ifP x else ifP y)
         = Pow $ \i -> Pow $ \j ->
           if p i
              then if p j then pure x else Zero
              then if p j then pure y else Zero

    (join . join) bad2
           -- Use (join-Pow-Pow)
       = join $ Pow $ \i ->
           if p i
             then if p i then pure x else Zero
             else if p i then pure x else Zero
       = join $ Pow $ \i ->
           if p i then pure x else Zero
       = join (ifP x)
           -- Use assumption
       = pure x

    (join . fmap join) bad2
           -- Use definition of fmap
       = join $ Pow $ \i -> if p i then join (ifP x) else join (ifP y)
           -- Use assumption
       = join $ Pow $ \i -> if p i then pure x else pure y
       = join $ Pow $ \i -> Pow $ if p i then const x else const y
       = Pow $ \i -> if p i then x else y

今、`(join . join) bad2`は`y`に依存しませんが、`(join . fmap join) bad2`は依存します。そのため、これらは一致しません。

したがって、2つ以上の異なる値があるような型`k`に対して、`F k`は`Monad`型になりません。
