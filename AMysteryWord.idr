module Main

import Effects
import Effect.StdIO
import Effect.Random
import Effect.System

import Data.So
import Data.Fin
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
                 (\inword =>
                        Mystery (case inword of
                             True => (Running (S g) w)
                             False => (Running g (S w))))
     Won  : sig MysteryRules () (Mystery (Running g 0))
                                (Mystery NotRunning)
     Lost : sig MysteryRules () (Mystery (Running 0 g))
                                (Mystery NotRunning)
     NewWord : (w : String) ->
               sig MysteryRules () h (Mystery (Running 6 (length (letters w))))
     Get : sig MysteryRules h h

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

instance Default (Mystery NotRunning) where
    default = Init

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

guess : Char -> Eff Bool
                [MYSTERY (Running (S g) (S w))]
                (\inword => [MYSTERY (case inword of
                                        True => Running (S g) w
                                        False => Running g (S w))])
guess c = call (Main.Guess c)

won :  Eff () [MYSTERY (Running g 0)] [MYSTERY NotRunning]
won = call Won

lost : Eff () [MYSTERY (Running 0 g)] [MYSTERY NotRunning]
lost = call Lost

new_word : (w : String) -> Eff () [MYSTERY h] 
                                  [MYSTERY (Running 6 (length (letters w)))]
new_word w = call (NewWord w)

get : Eff (Mystery h) [MYSTERY h]
get = call Get

instance Handler MysteryRules m where
    handle (MkG w g got []) Won k = k () (GameWon w)
    handle (MkG w Z got m) Lost k = k () (GameLost w)

    handle st Get k = k st st
    handle st (NewWord w) k = k () (initState w)

    handle (MkG w (S g) got m) (Guess x) k =
        case isElem x m of
             No _ => k False (MkG w _ got m)
             Yes p => k True (MkG w _ (x :: got) (shrink m p))

soRefl : So x -> (x = True)
soRefl Oh = Refl

game : Eff () [MYSTERY (Running (S g) w), STDIO]
              [MYSTERY NotRunning, STDIO]
game {w=Z} = won
game {w=S _}
     = do putStrLn (show !get)
          putStr "Enter guess: "
          let guess = trim !getStr
          case choose (not (guess == "")) of
               (Left p) => processGuess (strHead' guess (soRefl p))
               (Right p) => do putStrLn "Invalid input!"
                               game
  where
    processGuess : Char -> Eff () [MYSTERY (Running (S g) (S w)), STDIO]
                                  [MYSTERY NotRunning, STDIO]
    processGuess {g} c {w}
      = case !(guess c) of
             True => do putStrLn "Good guess!"
                        case w of
                             Z => won
                             (S k) => game
             False => do putStrLn "No, sorry"
                         case g of
                              Z => lost
                              (S k) => game

words : ?wtype
words = with Vect ["idris","agda","haskell","miranda",
         "java","javascript","fortran","basic",
         "coffeescript","rust"]

wtype = proof search

runGame : Eff () [MYSTERY NotRunning, RND, SYSTEM, STDIO]
runGame = do srand !time
             let w = index !(rndFin _) words
             new_word w
             game
             putStrLn (show !get)

main : IO ()
main = run runGame

