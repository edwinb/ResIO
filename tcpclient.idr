include "rawnet.idr";

main = do { sock <- _prim_socket INET Stream;
            r <- _prim_connect sock (HostPort "127.0.0.1" 4567);
            putStrLn (showInt r);
            pkt <- newPacket 32;
            _prim_send sock pkt;
            sleep 1;
            dg <- _prim_recv sock;
            putStrLn "Done";
};
