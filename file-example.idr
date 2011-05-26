include "ResIO.idr";

fread' : File -> IOr String;
fread' x = ior (fread x);

fopen' : String -> String -> IOr (Either () File);
fopen' f m = ior do { h <- fopen f m;
                      return (Right h); };

fclose' : File -> IOr ();
fclose' f = ior (fclose f);

rread : MK_USE File String;
rread r = USE fread' r;  %hide fread';

ropen : String -> MK_CREATE (Either () File);
ropen fname i = CREATE i (fopen' fname "r");  %hide fopen';

rclose : MK_UPDATE File ();
rclose r = UPDATE (fclose' (getResource r)) r;  %hide fclose';

do using (BIND, RETURN) {

  printline : ResSub File ();
  printline h = do { str <- rread h;
                     LIFT (putStrLn str); };

  oc : ResProg ();
  oc = RP {n=resources 1}
          do { ropen "Test" fO;
               h <- GET fO;
               CHECK h
                     (return II)
                     (do { h <- GET fO;
                           CALL printline h;
                           CALL printline h;
                           CALL printline h;
                           CALL printline h;
                           CALL printline h;
                           rclose h;
                         });
             };
}

main = run oc;
