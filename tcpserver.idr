include "rawnet.idr";

process : (SockID & SockAddr) -> IO ();
process (c, HostPort h p) = do { putStrLn "About to receive";
                                 pkt <- _prim_recv c;
                                 putStrLn ("Received from " ++ h ++ ":" ++ showInt p);
                                 _prim_send c pkt; 
                                 return II;
                               };

serverLoop : SockID -> IO ();
serverLoop sock = do { req <- _prim_accept sock;
                       process req; 
                       serverLoop sock;
                     };

main = do { sock <- _prim_socket INET Stream;
            r <- _prim_bind sock (Port 4567);
            putStrLn (showInt r);
            r <- _prim_listen sock 5;
            putStrLn (showInt r);
            serverLoop sock; };