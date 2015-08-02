module List.Split

data Delimiter a = MkDelimiter (List (a -> Bool))

data DelimPolicy = Drop | Keep | KeepLeft | KeepRight

data CondensePolicy = Condense | DropBlankFields | KeepBlankFields

data EndPolicy = DropBlank | KeepBlank

data Chunk a = Delim (List a) | Text (List a)

SplitList : Type -> Type
SplitList a = List (Chunk a)

record Splitter a where
  constructor MkSplitter
  delimiter : Delimiter a
  delimPolicy : DelimPolicy
  condensePolicy : CondensePolicy
  initBlankPolicy : EndPolicy
  finalBlankPolicy : EndPolicy

defaultSplitter : Splitter a
defaultSplitter =
  MkSplitter
  (MkDelimiter [const False])
  Keep
  KeepBlankFields
  KeepBlank
  KeepBlank

matchDelim : Delimiter a -> List a -> Maybe (List a, List a)
matchDelim (MkDelimiter []) xs = Just ([], xs)
matchDelim (MkDelimiter _) []  = Nothing
matchDelim (MkDelimiter (p::ps)) (x::xs) =
  if p x then matchDelim (MkDelimiter ps) xs >>= \(h, t) => Just (x::h, t)
         else Nothing

fromElem : Chunk a -> List a
fromElem (Delim as) = as
fromElem (Text as)  = as

isDelim : Chunk a -> Bool
isDelim (Delim _) = True
isDelim _         = False

isText : Chunk a -> Bool
isText = not . isDelim

breakDelim : Delimiter a -> List a -> (List a, Maybe (List a, List a))
breakDelim (MkDelimiter []) xs          = ([], Just ([], xs))
breakDelim _                []          = ([], Nothing)
breakDelim d                xxs@(x::xs) =
  case matchDelim d xxs of
    Nothing    => let (ys, match) = breakDelim d xs in (x::ys, match)
    Just match => ([], Just match)

splitInternal : Delimiter a -> List a -> SplitList a
splitInternal _ [] = []
splitInternal d xxs =
  let (xs, match) = breakDelim d xxs
  in if isNil xs then toSplitList match d
                 else Text xs :: toSplitList match d
  where
    toSplitList : Maybe (List a, List a) -> Delimiter a -> SplitList a
    toSplitList Nothing              d = []
    toSplitList (Just ([], r::rs))   d = Delim [] :: Text [r] :: splitInternal d rs
    toSplitList (Just (delim, rest)) d = Delim delim :: splitInternal d rest

doDrop : DelimPolicy -> SplitList a -> SplitList a
doDrop Drop l = filter isText l
doDrop _ l    = l

doCondense : CondensePolicy -> SplitList a -> SplitList a
doCondense Condense ls = condense' ls
  where condense' [] = []
        condense' (c@(Text _) :: l) = c :: condense' l
        condense' l = let (ds,rest) = span isDelim l
                      in (Delim $ concatMap fromElem ds) :: condense' rest
doCondense _ ls = ls

insertBlanks' : CondensePolicy -> SplitList a -> SplitList a
insertBlanks' _ [] = []
insertBlanks' cp@DropBlankFields (d1@(Delim _) :: d2@(Delim _) :: l) =
  d1 :: insertBlanks' cp (d2 :: l)
insertBlanks' cp (d1@(Delim _) :: d2@(Delim _) :: l) =
  d1 :: Text [] :: insertBlanks' cp (d2 :: l)
insertBlanks' _ [d@(Delim _)] = [d, Text []]
insertBlanks' cp (c :: l) = c :: insertBlanks' cp l

insertBlanks : CondensePolicy -> SplitList a -> SplitList a
insertBlanks _ [] = [Text []]
insertBlanks cp (d@(Delim _) :: l) = Text [] :: insertBlanks' cp (d :: l)
insertBlanks cp l = insertBlanks' cp l

mergeLeft : SplitList a -> SplitList a
mergeLeft [] = []
mergeLeft ((Delim d) :: (Text c) :: l) = Text (d ++ c) :: mergeLeft l
mergeLeft (c :: l) = c :: mergeLeft l

-- TODO: How to get typechecking?
--mergeRight : SplitList a -> SplitList a
--mergeRight [] = []
--mergeRight ((Text c) :: l) =
--  let
--    (d, lTail) =
--      case l of
--        (Delim d') :: l' => (d', l')
--        _                => ([], l)
--  in Text (c ++ d) :: mergeRight lTail
--mergeRight (c :: l) = c :: mergeRight l

doMerge : DelimPolicy -> SplitList a -> SplitList a
doMerge KeepLeft  = mergeLeft
doMerge KeepRight = id -- TODO: Fix when above is fixed. mergeRight
doMerge _         = id

dropInitial : EndPolicy -> SplitList a -> SplitList a
dropInitial DropBlank (Text [] :: l) = l
dropInitial _ l                      = l

dropFinal : EndPolicy -> SplitList a -> SplitList a
dropFinal _         [] = []
dropFinal DropBlank l  = dropFinal' l
  where dropFinal' []         = []
        dropFinal' [Text []]  = []
        dropFinal' (x::xs)    = x::dropFinal' xs
dropFinal _         l  = l

postProcess : Splitter a -> SplitList a -> SplitList a
postProcess s = dropFinal (finalBlankPolicy s)
              . dropInitial (initBlankPolicy s)
              . doMerge (delimPolicy s)
              . doDrop (delimPolicy s)
              . insertBlanks (condensePolicy s)
              . doCondense (condensePolicy s)

split : Splitter a -> List a -> List (List a)
split s = map fromElem . postProcess s . splitInternal (delimiter s)

oneOf : Eq a => List a -> Splitter a
oneOf elts = record { delimiter = MkDelimiter [(flip elem elts)] } defaultSplitter

onSublist : Eq a => List a -> Splitter a
onSublist lst = record { delimiter = MkDelimiter (map (==) lst) } defaultSplitter

whenElt : (a -> Bool) -> Splitter a
whenElt p = record { delimiter = MkDelimiter [p] } defaultSplitter

dropDelims : Splitter a -> Splitter a
dropDelims s = record { delimPolicy = Drop } s

keepDelimsL : Splitter a -> Splitter a
keepDelimsL s = record { delimPolicy = KeepLeft } s

keepDelimsR : Splitter a -> Splitter a
keepDelimsR s = record { delimPolicy = KeepRight } s

condense : Splitter a -> Splitter a
condense s = record { condensePolicy = Condense } s

dropInitBlank : Splitter a -> Splitter a
dropInitBlank s = record { initBlankPolicy = DropBlank } s

dropFinalBlank : Splitter a -> Splitter a
dropFinalBlank s = record { finalBlankPolicy = DropBlank } s

dropInnerBlanks : Splitter a -> Splitter a
dropInnerBlanks s = record { condensePolicy = DropBlankFields } s

dropBlanks : Splitter a -> Splitter a
dropBlanks = dropInitBlank . dropFinalBlank . condense

startsWith : Eq a => List a -> Splitter a
startsWith = dropInitBlank . keepDelimsL . onSublist

startsWithOneOf : Eq a => List a -> Splitter a
startsWithOneOf = dropInitBlank . keepDelimsL . oneOf

endsWith : Eq a => List a -> Splitter a
endsWith = dropFinalBlank . keepDelimsR . onSublist

endsWithOneOf : Eq a => List a -> Splitter a
endsWithOneOf = dropFinalBlank . keepDelimsR . oneOf

splitOneOf : Eq a => List a -> List a -> List (List a)
splitOneOf = List.Split.split . dropDelims . oneOf

splitOn : Eq a => List a -> List a -> List (List a)
splitOn = List.Split.split . dropDelims . onSublist

splitWhen : (a -> Bool) -> List a -> List (List a)
splitWhen = List.Split.split . dropDelims . whenElt

endBy : Eq a => List a -> List a -> List (List a)
endBy = List.Split.split . dropFinalBlank . dropDelims . onSublist

endByOneOf : Eq a => List a -> List a -> List (List a)
endByOneOf = List.Split.split . dropFinalBlank . dropDelims . oneOf

wordsBy : (a -> Bool) -> List a -> List (List a)
wordsBy = List.Split.split . dropBlanks . dropDelims . whenElt

linesBy : (a -> Bool) -> List a -> List (List a)
linesBy = List.Split.split . dropFinalBlank . dropDelims . whenElt

build : ((a -> List a -> List a) -> List a -> List a) -> List a
build g = g (::) []

chunksOf : Nat -> List e -> List (List e)
chunksOf i ls = map (take i) (build (splitter ls)) where
  splitter : List e -> (List e -> a -> a) -> a -> a
  splitter [] _ n = n
  splitter l c n  = l `c` splitter (drop i l) c n

splitPlaces : List Nat -> List e -> List (List e)
splitPlaces is ys = build (splitPlacer is ys) where
  splitPlacer : List Nat -> List b -> (List b -> t -> t) -> t -> t
  splitPlacer [] _ _ n         = n
  splitPlacer _ [] _ n         = n
  splitPlacer (l :: ls) xs c n = let (x1, x2) = splitAt l xs
                                 in  x1 `c` splitPlacer ls x2 c n

splitPlacesBlanks : List Nat -> List e -> List (List e)
splitPlacesBlanks is ys = build (splitPlacer is ys) where
  splitPlacer : List Nat -> List b -> (List b -> t -> t) -> t -> t
  splitPlacer [] _ _ n         = n
  splitPlacer (l :: ls) xs c n = let (x1, x2) = splitAt l xs
                                 in  x1 `c` splitPlacer ls x2 c n

chop : (List a -> (b, List a)) -> List a -> List b
chop _ [] = []
chop f as = let (b, as') = f as in b :: chop f as'
