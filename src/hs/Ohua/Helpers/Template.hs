module Ohua.Helpers.Template where

import Ohua.Prelude

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Attoparsec.Text as AP
import qualified Data.Functor.Foldable as RS
import Control.Category ((>>>))
import Control.Monad.Writer
import qualified Data.HashSet as HS
import qualified Data.Char as Char

import Ohua.Util (mapLeft)


type Template = FilePath
type Substitutions = HashMap.HashMap Text [ Text ]

data Opts = Opts
    { preserveSpace :: Bool
    }

data Rep
    = Replace Text Text
    | Keep Text

data Action
    = Insert
    | Begin
    | End
    deriving (Show)

toRep :: Text -> Either Text (Text, Action, Text)
toRep l = mapLeft (const l) $ AP.parseOnly specialLine l
  where
    specialLine = do
        sp <- AP.takeWhile Char.isSpace
        void $ AP.string "//"
        AP.skipSpace
        void $ AP.char '<'
        let token str tok = AP.string str >> pure tok
        ac <- token "insert" Insert <|> token "begin" Begin <|> token "end" End
        void $ AP.char '('
        key <- AP.takeTill (== ')')
        void $ AP.string ")>"
        AP.skipSpace
        AP.endOfInput
        pure (sp, ac, key)

parseTemplate :: Text -> [Rep]
parseTemplate =
    lines
    >>> RS.cata f
    >>> flip runReader Nothing
  where
    setSection v = local (const v)
    withEndSection :: MonadReader (Maybe a) m => m b -> m b
    withEndSection = setSection Nothing
    withBeginSection :: MonadReader (Maybe a) m => a -> m b -> m b
    withBeginSection = setSection . Just
    f = \case
        RS.Cons line cont -> do
            let appendCont e = (e:) <$> cont
            sec <- ask
            case toRep line of
                Right (sp, action, key)
                    | Just key' <- sec ->
                      case action of
                          End | key' == key ->
                                withEndSection $ appendCont (Replace sp key)
                          _ -> error $ "Unexpected action or key. Expected <begin(" <> key' <> " got " <> show action <> "(" <> key <> ")"
                    | otherwise ->
                        case action of
                            Insert | Just k <- sec -> error $ "Insert in section '" <> k <> "'"
                                   | otherwise -> appendCont (Replace sp key)
                            Begin -> withBeginSection key cont
                            End -> error $ "End of unopened section '" <> key <> "'"
                Left toKeep | Nothing <- sec -> appendCont (Keep toKeep)
                            | otherwise -> cont
        RS.Nil -> pure []

sub :: MonadLogger m => Opts -> [Rep] -> Substitutions -> m Text
sub Opts{..} subl subs = do
    (lines_, replaced) <- execWriterT $ for_ subl $ \case
        Keep l -> writeLine l
        Replace sp key
            | Just t <- HashMap.lookup key subs -> do
                  writeSpaced sp $ marked key (t >>= lines)
                  writeReplaced key
            | otherwise -> do
                  logErrorN $ "Key '" <> key <> "' not found in substitutions"
                  writeSpaced sp $ marked key []
    let unsubstituted = HS.fromMap (fmap (const ()) subs) `HS.difference` replaced
    unless (HS.null unsubstituted) $
        logWarnN $ "Substitution keys " <> show ( HS.toList unsubstituted ) <> " were not used."
    pure $ unlines lines_
  where
    beginMarker key = "// <begin(" <> key <> ")>"
    endMarker key = "// <end(" <> key <> ")>"
    writeSpaced sp = writeLines . (if preserveSpace then map (sp <>) else id)
    writeLines = tell . (,mempty)
    writeLine = writeLines . pure
    writeReplaced = tell . (mempty,) . HS.singleton
    marked key l = beginMarker key : l <> [endMarker key]
