include "rawnet.idr";

dump : (RawPacket & SockAddr) -> IO ();
dump (pkt, HostPort h p) = putStrLn ("Received stuff from " ++ h ++ ":" ++
                                     showInt p);
dump (pkt, _) = putStrLn ("Got nothing");

main = do { sock <- _prim_socket INET Datagram;
            pkt <- newPacket 32;
            -- r <- _prim_bind sock (Port 0);
            _prim_sendTo sock pkt (HostPort "127.0.0.1" 4567);
            sleep 1;
            dg <- _prim_recvFrom sock;
            dump dg;
};
