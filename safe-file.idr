include "ResIO.idr";

data Purpose = Reading | Writing;

data FState = Open Purpose | Closed;

data FILE : FState -> Set where
    OpenH   : File -> FILE (Open p)
  | ClosedH : FILE Closed;

data FileError = OpenFailed;

open_r      : String -> (p:Purpose) -> 
              IOr (Either (FILE Closed) (FILE (Open p)));
close_r     : FILE (Open p) -> IOr (FILE Closed);
readLine_r  : FILE (Open Reading) -> IOr String;
writeLine_r : String -> FILE (Open Writing) -> IOr ();
eof_r       : FILE (Open Reading) -> IOr Bool;

pstring : Purpose -> String;
pstring Reading = "r";
pstring Writing = "w";

open_r fn p = ior do { h <- fopen fn (pstring p);
                       if (validFile h) then (return (Right (OpenH h))) 
                                        else (return (Left ClosedH)); };

close_r         (OpenH f) = ior (do { fclose f; return ClosedH; });
readLine_r      (OpenH f) = ior (fread f);
writeLine_r str (OpenH f) = ior (fwrite f str);
eof_r           (OpenH f) = ior (feof f);

%hide OpenH;
%hide ClosedH;

open : String -> (p:Purpose) -> 
       MK_CREATE (Either (FILE Closed) (FILE (Open p)));
open fname p i = CREATE i (open_r fname p);    %hide fopen;

close : MK_UPDATE (FILE (Open p)) (FILE Closed);
close r = UPDATE (close_r (getResource r)) r;  %hide fclose;

readLine : MK_USE (FILE (Open Reading)) String;
readLine r = USE readLine_r r;                 %hide fread;

writeLine : String -> MK_USE (FILE (Open Writing)) ();
writeLine str r = USE (writeLine_r str) r;     %hide fwrite;

eof : MK_USE (FILE (Open Reading)) Bool;
eof r = USE eof_r r;                           %hide feof;

----

do using (BIND, RETURN) {

  readFile' : String -> ResSub (FILE (Open Reading)) String;
  readFile' acc h 
     = do { end <- eof h;
            if end then (return acc)
                   else (do { str <- readLine h;
                              CALL (readFile' (acc ++ str ++ "\n")) h; });
          };

  readFile : ResSub (FILE (Open Reading)) String;
  readFile h = CALL (readFile' "") h;

  test : ResProg ();
  test = RP {n=resources 1}
         do { open "Test" Reading fO;
              h <- GET fO;
              CHECK h (LIFT (putStrLn "File open error"))
                      (do { h <- GET fO;
                            content <- CALL readFile h;
                            LIFT (putStrLn content);
                            close h; 
                            return II;
                          });
            };

}

main = run test;
