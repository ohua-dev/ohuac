module Ohua.Helpers.Template where

import Ohua.Prelude

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Attoparsec.Text as AP
import qualified Data.Functor.Foldable as RS
import Ohua.Util (mapLeft)
import Control.Category ((>>>))


type Template = FilePath
type Substitutions = HashMap.HashMap Text Text

data Rep
    = Replace Text
    | Keep Text

data Action
    = Insert
    | Begin
    | End
    deriving (Show)

toRep :: Text -> Either Text (Action, Text)
toRep l = mapLeft (const l) $ AP.parseOnly specialLine l
  where
    specialLine = do
        void $ AP.string "//"
        AP.skipSpace
        void $ AP.char '<'
        let token str tok = AP.string str >> pure tok
        ac <- token "insert" Insert <|> token "begin" Begin <|> token "end" End
        void $ AP.char '('
        key <- AP.takeTill (== ')')
        AP.skipSpace
        AP.endOfInput
        pure (ac, key)

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
                Right (action, key)
                    | Just key' <- sec ->
                      case action of
                          End | key' == key ->
                                withEndSection $ appendCont (Replace key)
                          _ -> error $ "Unexpected action or key. Expected <begin(" <> key' <> " got " <> show action <> "(" <> key <> ")"
                    | otherwise ->
                        case action of
                            Insert | Just k <- sec -> error $ "Insert in section '" <> k <> "'"
                                   | otherwise -> appendCont (Replace key)
                            Begin -> withBeginSection key cont
                            End -> error $ "End of unopened section '" <> key <> "'"
                Left toKeep | Nothing <- sec -> appendCont (Keep toKeep)
                            | otherwise -> cont
        RS.Nil -> pure []

sub :: [Rep] -> Substitutions -> Text
sub subl subs = unlines $ subl >>= \case
    Keep l -> [l]
    Replace key
        | Just t <- HashMap.lookup key subs -> [beginMarker key, t, endMarker key]
        | otherwise -> error $ "Key '" <> key <> "' not found in substitutions"
  where
    beginMarker key = "// <begin(" <> key <> ")>"
    endMarker key = "// <end(" <> key <> ")>"
