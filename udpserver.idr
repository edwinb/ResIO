include "rawnet.idr";
-- include "IPDSL.idr";

dump : (RawPacket & SockAddr) -> IO ();
dump (pkt, HostPort h p) = putStrLn ("Received stuff from " ++ h ++ ":" ++
                                     showInt p);
dump (pkt, _) = putStrLn ("Got nothing");

main = do { sock <- _prim_socket INET Datagram;
            r <- _prim_bind sock (Port 4567);
            putStrLn (showInt r);
            dg <- _prim_recvFrom sock;
            r <- _prim_sendTo sock (fst dg) (snd dg); -- send an echo;
            putStrLn (showInt r);
            dump dg; };
