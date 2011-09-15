include "resimp.idr";

pstring : Purpose -> String;
pstring Reading = "r";
pstring Writing = "w";

data Purpose = Reading | Writing;

data FILE : Purpose -> Set where
    OpenH   : File -> FILE p;

open : String -> (p:Purpose) -> Creator (Either () (FILE p));
open fn p = ioc do { h <- fopen fn (pstring p);
                     if (validFile h) then (return (Right (OpenH h)))
                                      else (return (Left II)); };

close : FILE p -> Updater ();
close (OpenH h) = iou (fclose h);

readLine : FILE Reading -> Reader String;
readLine (OpenH h) = ior (fread h);

eof : FILE Reading -> Reader Bool;
eof (OpenH h) = ior (feof h);

syntax rclose h = Update close h;
syntax rreadLine h = Use readLine h;
syntax reof h = Use eof h;

syntax rputStrLn s = Lift (putStrLn s);

readH : String -> (FILE Reading :-> R ());
readH intro h = res (While (do { end <- reof h;
                                 return (not end); })
                           (do { str <- rreadLine h;
                                 rputStrLn (intro ++ str); }));

readCloseH : String -> (FILE Reading |-> Val ());
readCloseH intro h = res do { While (do { end <- reof h;
                                          return (not end); })
                                    (do { str <- rreadLine h;
                                          rputStrLn (intro ++ str); });
                              rclose h; };

-- syntax rreadH i h = Call (readH i) (ACons h ANil);

testprog : String -> RES ();
testprog filename 
    = res do { let h = open filename Reading;
               let h' = open filename Reading;
               Check h
                 (rputStrLn "File open error")
                 (do { readH "Line: " h;
                       rclose h; 
                       rputStrLn "DONE"; });
               Check h'
                 (rputStrLn "File open error")
                 (do { readCloseH "Line: " h';
                       rputStrLn "DONE"; });
             };

main : IO ();
main = do { x <- run (testprog "Test");
            return x; };
