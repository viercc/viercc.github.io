---
title: モナドになれないFunctor
---

## モナドになれないFunctor (A Functor which can't be a Monad)

このFunctorをMonadにする方法があるだろうか？

    data F2 x = Z | P x x
      deriving (Functor)

    pure :: forall x. x -> F2 x
    join :: forall x. F2 (F2 x) -> F2 x

It's easy to prove `pure x ≠ Z`, because `join . pure = id`.
So it must be:

    pure x = P x x   -- (1)

What about join?　Trivially, when called with an argument which have
no `x` value, it have to return `Z`.

    join Z = Z           -- (2)
    join (P Z Z) = Z     -- (3)

From the Monad law,

    -- join . pure = id
    join (P mx mx) = mx
    join (P (P x y) (P x y)) = P x y      -- (4)

    -- join . fmap pure = id
    join $ fmap pure (P x y)
      = join (P (P x x) (P y y)) = P x y  -- (5)

To satisfy (4) and (5) simultaneously, it must be:

    join (P (P x y) (P z w)) = P x w      -- (6)

To satisfy another Monad law, associativity, the following must hold.

    join . join = join (fmap join)

What `join` should return in the following case?

    join (P (P x y) Z) = ???

(Case-Z) If `??? = Z`, then

    bad1 = P (P (P x y) Z      )
             (P Z       (P z w))

    (join . join)      bad1 = join (P (P x y) (P z w)) = P x w
    (join . fmap join) bad1 = join (P Z (join (P Z (P z w)))) ≠ P x w

(Case-P) If `??? = P (s x y) (t x y)` for some functions `s, t :: forall x. x -> x -> x`, Then

    bad2 = P (P (P x y) Z)
             (P (P z w) Z)

    (join . join) bad2
      = join $ P (P x y) Z
      = P (s x y) (t x y)
    (join . fmap join) bad2
      = join $ P (P (s x y) (t x y))
                 (P (s z w) (t z w))
      = P (s x y) (t z w)
      ≠ P (s x y) (t x y)

Thus there can be no lawful Monad instance!

## 一般化しよう

    data F k x = Zero | Pow (k -> x)
        deriving (Functor)

From the same arguent to above `F2`,

    pure :: forall x. x -> F k 
    pure x = Pow (const x)

And

    join Zero = Zero
    join (Pow $ \_ -> Zero) = Zero
    join $ Pow (\i -> Pow (\j -> f i j)) = Pow (\i -> f i i)  -- (join-Pow-Pow)
      -- join $ Pow (\_ -> Pow f)           = Pow f
      -- join $ Pow (\i -> Pow (\_ -> f i)) = Pow f

Assume `k` has two or more distinct values and there is a way to discriminate them, i.e.

    -- p truthy = True
    -- p falsy = False
    p :: k -> Bool
    truthy, falsy :: k

    ifP, unlessP :: forall x. (k -> x) -> F k (F k x)
    ifP f = Pow (\i -> if p i then Pow f else Zero)
    unlessP f = Pow (\i -> if p i then Zero else Pow f)

What `join` should return in this case?

    join (ifP f) = ???

Suppose `join (ifP f) = Zero`, then

    -- free parameters
    type A :: *
    f, g :: k -> A
    
    bad1 :: F k (F k (F k A))
    bad1 = Pow (\i -> if p i then ifP f else unlessP g)
           -- Notice that both `ifP` and `unlessP` returns `Pow _`
         = Pow $ \i -> Pow $ \j ->
             if p i
               then if p j then Pow f else Zero
               else if p j then Zero  else Pow g

    (join . join) bad1
         -- Use (join-Pow-Pow)
       = join $ Pow $ \i ->
           if p i
             then if p i then Pow f else Zero
             else if p i then Zero  else Pow g
       = join $ Pow \i -> if p i then Pow f else Pow g
       = join $ Pow \i -> Pow $ if p i then f else g
       = Pow $ \i -> if p i then f i else g i

    (join . fmap join) bad1
         -- Use definition of fmap
       = join $ Pow $ \i -> if p i then join (ifP f) else join (unlessP g)
         -- Use the assumption: join (ifP f) = Zero
       = join $ Pow $ \i -> if p i then Zero else join (unlessP g)

Since `(join . join) bad1` depends on `f` but `(join . fmap join) bad1` doesn't, `join . join ≠ join . fmap join`.

Suppose `join (ifP f) = Pow (s f)` for some function (`s :: forall x. (k -> x) -> k -> x`), then

    bad2 :: F k (F k (F k A))
    bad2 = Pow (\i -> if p i then ifP f else ifP g)
         = Pow $ \i -> Pow $ \j ->
           if p i
              then if p j then Pow f else Zero
              then if p j then Pow g else Zero

    (join . join) bad2
           -- Use (join-Pow-Pow)
       = join $ Pow $ \i ->
           if p i
             then if p i then Pow f else Zero
             else if p i then Pow g else Zero
       = join $ Pow $ \i ->
           if p i then Pow f else Zero
       = join (ifP f)
           -- Use assumption
       = Pow (s f)

    (join . fmap join) bad2
           -- Use definition of fmap
       = join $ Pow $ \i -> if p i then join (ifP f) else join (ifP g)
           -- Use assumption
       = join $ Pow $ \i -> if p i then Pow (s f) else Pow (s g)
       = join $ Pow $ \i -> Pow $ if p i then s f else s g
       = Pow $ \i -> if p i then s f i else s g i

Since `(join . join) bad2` doesn't depend on `g` but `(join . fmap join) bad2` does, `join . join ≠ join . fmap join`.

Thus, no return values satisfy the Monad law for `join (ifP f)`.

Conclusion: for any type `k` with two or more (discriminatable) values, `F k` can't be a Monad.

