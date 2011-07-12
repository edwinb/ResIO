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

readH : RESFN (FILE Reading :-> R ());
readH = res (\h => Fn (While (do { end <- Use eof h;
                                   return (not end); })
                             (do { str <- Use readLine h;
                                   Lift (putStrLn str); })));

testprog : String -> RES ();
testprog filename 
    = res do { let h = open filename Reading;
               Check h
                 (Lift (putStrLn "File open error"))
                 (do { Call readH (ACons h ANil);
                       Update close h; 
                       Lift (putStrLn "DONE"); });
             };

main : IO ();
main = do { x <- run (testprog "Test");
            return x; };