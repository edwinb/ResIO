module main

import resimpnew

data Purpose = Reading | Writing

pstring : Purpose -> String
pstring Reading = "r"
pstring Writing = "w"

data FILE : Purpose -> Set where
    OpenH : File -> FILE p

syntax ifM [test] then [t] else [e]
    = test >>= (\b => if b then t else e)

open : String -> (p:Purpose) -> Creator (Either () (FILE p))
open fn p = ioc (do h <- fopen fn (pstring p)
                    ifM (validFile h) then (return (Right (OpenH h)))
                         else (return (Left ())))

close : FILE p -> Updater ()
close (OpenH h) = iou (closeFile h)

readLine : FILE Reading -> Reader String
readLine (OpenH h) = ior (fread h)

eof : FILE Reading -> Reader Bool
eof (OpenH h) = ior (feof h)

syntax rclose [h]    = Update close h
syntax rreadLine [h] = Use readLine h
syntax reof [h]      = Use eof h

syntax rputStrLn [s] = Lift (putStrLn s)

syntax if opened [f] then [t] else [e] = Check f t e

readH : String -> RES ()
readH fn = res (do let x = open fn Reading
                   if opened x
                      then rputStrLn "Error"
                      else do str <- rreadLine stop
                              rputStrLn str
                              rclose stop)

main : IO ()
main = run (readH "Test")

