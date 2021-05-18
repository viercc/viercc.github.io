--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Hakyll
import           Hakyll.Web.Pandoc
import Text.Pandoc.Options

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

main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler
    
    match "images/*/*" $ do
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

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler' (Just katex)
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            postsAll <- recentFirst =<< loadAll "posts/*"
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
            posts15 <- fmap (take 15) $ recentFirst =<< loadAll "posts/*"
            let indexCtx =
                     listField "posts" postCtx (return posts15)
                  <> constField "title" "Home"
                  <> defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler

--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
     dateField "date" "%F"
  <> defaultContext
