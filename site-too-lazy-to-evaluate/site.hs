--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
import           Hakyll
import           Hakyll.Web.Pandoc
import Text.Pandoc.Options
import Data.Time.Format

import Control.Monad.Except (ExceptT(..), MonadTrans (lift))
import Control.Applicative
import Data.Ord
import Data.List (sortBy)
import Data.Time (UTCTime)
import Data.Bifunctor (second)

------------------------------------


defaultOptions :: (ReaderOptions, WriterOptions)
defaultOptions = (reader', writer')
  where
    ext =
      enableExtension Ext_footnotes .
      disableExtension Ext_tex_math_dollars

    reader = defaultHakyllReaderOptions
    reader' = reader{ readerExtensions = ext (readerExtensions reader)}

    writer = defaultHakyllWriterOptions
    writer' = writer{ writerExtensions = ext (writerExtensions writer)}

setMathOpt ::
     Maybe HTMLMathMethod
  -> (ReaderOptions, WriterOptions)
  -> (ReaderOptions, WriterOptions)
setMathOpt Nothing opts = opts
setMathOpt (Just htmlMath) (reader, writer) = (reader', writer')
  where
    mathExts = enableExtension Ext_tex_math_double_backslash

    rx = readerExtensions reader
    reader' = reader{ readerExtensions = mathExts rx }
    wx = writerExtensions writer
    writer' = writer{
        writerExtensions = mathExts wx
      , writerHTMLMathMethod = htmlMath
      }

pandocCompiler' :: Maybe HTMLMathMethod -> Compiler (Item String)
pandocCompiler' mathOpt = pandocCompilerWith readerOpt writerOpt
  where
    (readerOpt, writerOpt) = setMathOpt mathOpt defaultOptions

katex :: HTMLMathMethod
katex = KaTeX defaultKaTeXURL

data BuildMode = PreviewMode | DeployMode
  deriving (Show, Eq)

mainRule :: BuildMode -> Rules ()
mainRule mode = do
    match "images/**" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    -- TODO: run any minifier
    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler

    match (fromList ["about.rst", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler' Nothing
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    let postsPub = "posts/*"
        postsStub = "posts/stub/*"

        posts = case mode of
            PreviewMode -> postsPub .||. postsStub
            DeployMode  -> postsPub

        postCompiler = pandocCompiler' (Just katex)
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    match postsPub $ do
        route $ setExtension "html"
        compile postCompiler

    match postsStub $ do
        case mode of
            PreviewMode -> route $ setExtension "html"
            DeployMode  -> return ()
        compile postCompiler

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            postsAll <- recentFirst' =<< loadAll posts
            let archiveCtx =
                     listField "posts" postCtx (return postsAll)
                  <> constField "title" "Archive"
                  <> defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            posts15 <- fmap (take 15) $ recentFirst' =<< loadAll posts
            let indexCtx =
                     listField "posts" postCtx (return posts15)
                  <> constField "title" "Home"
                  <> defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler

main :: IO ()
main = do
    let config = defaultConfiguration
    opt <- defaultParser config
    let mode = case optCommand opt of
          Watch{} -> PreviewMode
          _       -> DeployMode
    hakyllWithArgs config opt (mainRule mode)

--------------------------------------------------------------------------------

newtype TrapFail m a = Trap { runTrap :: m (Either String a) }
  deriving (Functor, Applicative, Monad) via (ExceptT String m)
  deriving (MonadTrans) via (ExceptT String)

instance Monad m => MonadFail (TrapFail m) where
    fail message = Trap $ return (Left message)

instance MonadMetadata m => MonadMetadata (TrapFail m) where
  getMetadata = lift . getMetadata
  getMatches = lift . getMatches

tryGetItemUTC :: (MonadMetadata m) => Item a -> m (Either String UTCTime)
tryGetItemUTC = runTrap . getItemUTC defaultTimeLocale . itemIdentifier

safeDateField :: String -> String -> Context a
safeDateField key format = field key $ \i -> do
    err_or_time <- tryGetItemUTC i
    case err_or_time of
        Left err   -> return err
        Right time -> return $ formatTime defaultTimeLocale format time

recentFirst' :: (MonadMetadata m) => [Item a] -> m [Item a]
recentFirst' = sortOnM (fmap (second Down) . tryGetItemUTC)

sortOnM :: (Monad m, Ord b) => (a -> m b) -> [a] -> m [a]
sortOnM f = fmap (map fst . sortBy (comparing snd)) . revmapM (\a -> fmap (a,) (f a))

revmapM :: (Monad m) => (a -> m b) -> [a] -> m [b]
revmapM f = go []
  where
    go acc [] = return acc
    go acc (a:as) = f a >>= \b -> go (b:acc) as

postCtx :: Context String
postCtx =
     safeDateField "date" "%F"
  <> defaultContext
