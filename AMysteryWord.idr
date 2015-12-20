import Effects

total
letters : String -> List Char
letters x with (strM x)
  letters "" | StrNil = []
  letters (strCons y xs) | (StrCons y xs) 
          = let xs' = assert_total (letters xs) in
                if ((not (isAlpha y)) || (y `elem` xs')) then xs' else y :: xs'

data GState = Running Nat Nat | NotRunning

data Mystery : GState -> Type

data MysteryRules : Effect where
     Guess : (x : Char) ->
             sig MysteryRules Bool
                 (Mystery (Running (S g) (S w)))
                 (\inword => if inword
                             then Mystery (Running (S g) w)
                             else Mystery (Running g (S w)))
     Won  : sig MysteryRules () (Mystery (Running g 0))
                                (Mystery NotRunning)
     Lost : sig MysteryRules () (Mystery (Running 0 g))
                                (Mystery NotRunning)
     NewWord : (w : String) ->
               sig MysteryRules () (Mystery NotRunning) (Mystery (Running 6 (length (letters w))))
     Get : sig MysteryRules String (Mystery h)

MYSTERY : GState -> EFFECT
MYSTERY h = MkEff (Mystery h) MysteryRules


