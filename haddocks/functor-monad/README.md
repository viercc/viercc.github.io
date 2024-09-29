# functor-monad: Monads on category of Functors

This package provides `FFunctor` and `FMonad`,
each corresponds to `Functor` and `Monad` but higher-order.

|      | a Functor `f`   | a FFunctor `ff` |
|----|----|----|
| Takes | `a :: Type` | `g :: Type -> Type`, `Functor g` |
| Makes | `f a :: Type` | `ff g :: Type -> Type`, `Functor (ff g)` |
| Methods | `fmap :: (a -> b) -> f a -> f b` | `ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)` |

|      | a Monad `m`   | a FMonad `mm` |
|----|----|----|
| Superclass | Functor | FFunctor |
| Methods | `return = pure :: a -> m a` | `fpure :: (Functor g) => g ~> mm g` |
|        | `(=<<) :: (a -> m b) -> m a -> m b` | `fbind :: (Functor g, Functor h) => (g ~> mm h) -> (mm g ~> mm h)` |
|        | `join :: m (m a) -> m a` | `fjoin :: (Functor g) => mm (mm g) ~> mm g` |

See also: https://viercc.github.io/blog/posts/2020-08-23-fmonad.html (Japanese article)

## Motivational examples

Many types defined in [base](https://hackage.haskell.org/package/base-4.18.1.0) and popolar libraries like
[transformers](https://hackage.haskell.org/package/transformers-0.6.1.1) take a parameter expecting a `Functor`.
Here are two, simple examples.

```haskell
-- From "base", Data.Functor.Sum
data Sum f g x = InL (f x) | InR (g x)
instance (Functor f, Functor g) => Functor (Sum f g)

-- From "transformers", Control.Monad.Trans.Reader
newtype ReaderT r m x = ReaderT { runReaderT :: r -> m x }
instance (Functor m) => Functor (ReaderT r m)
```

These types often have a way to map a natural transformation, an arrow between two `Functor`s,
over that parameter.

```haskell
-- The type of natural transformations
type (~>) f g = forall x. f x -> g x

mapRight :: (g ~> g') -> Sum f g ~> Sum f g'
mapRight _  (InL fx) = InL fx
mapRight nt (InR gx) = InR (nt gx)

mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b

-- mapReaderT can be used to map natural transformation
mapReaderT' :: (m ~> n) -> (ReaderT r m ~> ReaderT r n)
mapReaderT' naturalTrans = mapReaderT naturalTrans
```

The type class `FFunctor` abstracts type constructors equipped with such a function.

```haskell
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> ff g x -> ff h x

ffmap :: (Functor g, Functor g') => (g ~> g') -> Sum f g x -> Sum f g' x
ffmap :: (Functor m, Functor n)  => (m ~> n) -> ReaderT r m x -> ReaderT r n x
```

Not all but many `FFunctor` instances can, in addition to `ffmap`, support `Monad`-like operations.
This package provide another type class `FMonad` to represent such operations.

```haskell
class (FFunctor mm) => FMonad mm where
    fpure :: (Functor g) => g ~> mm g
    fbind :: (Functor g, Functor h) => (g ~> ff h) -> ff g a -> ff h a
```

Both of the above examples, `Sum` and `ReaderT r`, have `FMonad` instances.

```haskell
instance Functor f => FMonad (Sum f) where
    fpure :: (Functor g) => g ~> Sum f g
    fpure = InR

    fbind :: (Functor g, Functor h) => (g ~> Sum f h) -> Sum f g a -> Sum f h a
    fbind _ (InL fa) = InL fa
    fbind k (InR ga) = k ga

instance FMonad (ReaderT r) where
    fpure :: (Functor m) => m ~> ReaderT r m
    -- return :: x -> (e -> x)
    fpure = ReaderT . return

    fbind :: (Functor m, Functor n) => (m ~> ReaderT r n) -> ReaderT r m a -> ReaderT r n a
    -- join :: (e -> e -> x) -> (e -> x)
    fbind k = ReaderT . (>>= runReaderT . k) . runReaderT 
```

## Comparison against similar type classes

There are packages with very similar type classes, but they are more or less different to this package.

* From [hkd](https://hackage.haskell.org/package/hkd): `FFunctor`
  
  There is a class named `FFunctor` in `hkd` package too. It represents a functor from /category of type constructors/ `k -> Type` to
  the category of usual types and functions.

  Since it is not an endofunctor, there can be no `Monad`-like classes on them.

  Another package [rank2classes](https://hackage.haskell.org/package/rank2classes) also provides the same class `Rank2.Functor`.
  
* From [mmorph](https://hackage.haskell.org/package/mmorph-1.2.0): `MFunctor`, `MMonad`

  `MFunctor` is a class for endofunctors on the category of `Monad`s and monad homomorphisms.
  If `T` is a `MFunctor`, it takes a `Monad m` and constructs `Monad (T m)`,
  and its `hoist` method takes a *Monad morphism* `m ~> n` and returns a new *Monad morphism* `T m ~> T n`.

  On the other hand, this library is about endofunctors on the category of `Functor`s and natural transformations,
  which are similar but definitely distinct concept.

  For example, `Sum f` in the example above is not an instance of `MFunctor`, since there are no general way to make `Sum f m` a `Monad`
  for arbitrary `Monad m`.

  ```
  instance Functor f => FFunctor (Sum f)
  instance Functor f => MFunctor (Sum f) -- Can be written, but it will violate the requirement to be MFunctor
  ```

* From [index-core](https://hackage.haskell.org/package/index-core): `IFunctor`, `IMonad`

  They are endofunctors on the category of type constructors of kind `k -> Type` and polymorphic functions `t :: forall (x :: k). f x -> g x`.
  
  While any instance of `FFunctor` from this package can be faithfully represented as a `IFunctor`, some instances can't be an instance of `IFunctor` _as is_.
  Most notably, [Free](https://hackage.haskell.org/package/free-5.1.8/docs/Control-Monad-Free.html#t:Free) can't be an instance of `IFunctor` directly,
  because `Free` needs `Functor h` to be able to implement `fmapI`, the method of `IFunctor`.

  ```haskell
  class IFunctor ff where
    fmapI :: (g ~> h) -> (ff g ~> ff h)
  ```

  There exists a workaround: you can use another representation of `Free f` which doesn't require `Functor f` to be a `Functor` itself,
  for example `Program` from [operational](https://hackage.haskell.org/package/operational) package.

  This package avoids the neccesity of the workaround by admitting the restriction that the parameter of `FFunctor` must always be a `Functor`.
  Therefore, `FFunctor` gives up instances which don't take `Functor` parameter, for example, a type constructor `F` with kind `F :: (Nat -> Type) -> Nat -> Type`.

* From [functor-combinators](https://hackage.haskell.org/package/functor-combinators-0.4.1.2): `HFunctor`, `Inject`, `HBind`

  This package can be thought of as a more developed version of `index-core`, since they share the base assumption.
  The tradeoff between this package is the same: some `FFunctor` instances can only be `HFunctor` via alternative representations.
  Same applies for `FMonad` versus `Inject + HBind`.
