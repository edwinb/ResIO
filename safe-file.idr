include "ResIO.idr";

data Purpose = Reading | Writing;

data FState = Open Purpose | Closed;

data FILE : FState -> Set where
    OpenH   : File -> FILE (Open p)
  | ClosedH : FILE Closed;

data FileError = OpenFailed;

{-- Primitive operations. Defined as ordinary IO functions, then lifted into
    IOr.

    Living in IOr means they can only be called from
    a ResIO program, so we can guarantee that old resources (e.g. file handles
    that are no longer valid because they've been closed) are not accessible.

    Mostly the types just describe the state transitions of the resource in
    question. open_r is a bit trickier, because opening a file might fail.
--}

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

{-- Convert the primitive operations to ResIO operations. The type says 
    exactly what happens to the resource each function operates on, i.e.
    it's creating or updating a resource (which invalidates old resources)
    or it's just accessing a resource (which doesn't invalidate anything).

--}

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

  {-- Reading a file involves reading lines until we get to the end.
      A ResSub is a subroutine which uses a resource but mustn't change the
      resource state. Handy if, say, we have a resource we want to use a lot,
      like a file handle being passed around. 

      (Might be useful to make this more generic, if we want to pass around
      multiple resources/)
  --}

  readFile' : String -> ResSub (FILE (Open Reading)) String;
  readFile' acc h 
     = do { end <- eof h;
            if end then (return acc)
                   else (do { str <- readLine h;
                              CALL (readFile' (acc ++ str ++ "\n")) h; });
          };

  readFile : ResSub (FILE (Open Reading)) String;
  readFile h = CALL (readFile' "") h;

  data AllClosed : Vect ResTy n -> Set where
     ClosedNil  : AllClosed VNil
   | ClosedMore : {xs:Vect ResTy n} ->
                  AllClosed xs -> AllClosed (RTy (FILE Closed) :: xs);

  {-- A valid File program is a ResIO program paired with a proof that all
      the files it has used are closed at the end. --}

  test : VerProg (resources 1) AllClosed ();
  test = VP do { open "Test" Reading fO;
                 h <- GET fO;
                 CHECK h (LIFT (putStrLn "File open error"))
                         (do { h <- GET fO;
                               content <- CALL readFile h;
                               LIFT (putStrLn content);
                               close h; 
                               return II;
                             });
               } (ClosedMore ClosedNil);

}

main = vrun test;
