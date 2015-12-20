import Effects

import Data.Vect

total
letters : String -> List Char
letters x with (strM x)
  letters "" | StrNil = []
  letters (strCons y xs) | (StrCons y xs) 
          = let xs' = assert_total (letters xs) in
                if ((not (isAlpha y)) || (y `elem` xs')) then xs' else y :: xs'

instance Uninhabited (Elem x []) where
    uninhabited Here impossible

shrink : (xs : Vect (S n) a) -> Elem x xs -> Vect n a
shrink (x :: ys) Here = ys
shrink (y :: []) (There p) = absurd p
shrink (y :: (x :: xs)) (There p) = y :: shrink (x :: xs) p

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

data Mystery : GState -> Type where
     Init     : Mystery NotRunning
     GameWon  : (word : String) -> Mystery NotRunning
     GameLost : (word : String) -> Mystery NotRunning
     MkG      : (word : String) ->
                (guesses : Nat) ->
                (got : List Char) ->
                (missing : Vect m Char) ->
                Mystery (Running guesses m)

instance Show (Mystery s) where
    show Init = "Not ready yet"
    show (GameWon w) = "You won! Successfully guessed " ++ w
    show (GameLost w) = "You lost! The word was " ++ w
    show (MkG w guesses got missing)
         = let w' = pack (map showGot (unpack w)) in
               w' ++ "\n\n" ++ show guesses ++ " guesses left"
      where showGot : Char -> Char
            showGot ' ' = '/'
            showGot c = if ((not (isAlpha c)) || (c `elem` got)) then c else '-'

initState : (x : String) -> Mystery (Running 6 (length (letters x)))
initState w = let xs = letters w in
                  MkG w _ [] (fromList (letters w))

instance Handler MysteryRules m where
    handle (MkG w g got []) Won k = k () (GameWon w)
    handle (MkG w Z got m) Lost k = k () (GameLost w)

    handle st Get k = k (show st) st
    handle st (NewWord w) k = k () (initState w)

    handle (MkG w (S g) got m) (Guess x) k =
        case isElem x m of
             No _ => k False (MkG w _ got m)
             Yes p => k True (MkG w _ (x :: got) (shrink m p))

