include "bittwiddle.idr"; -- for packet formats

%include "rawnet.h"
%lib "rawnet.o"

data SockID = MkSock Int;

data SocketType = Stream | Datagram;
data Family     = UNIX   | INET;
data RW         = Read   | Write;

data SockAddr   = HostPort String Int | Port Int; 

_prim_socket  : Family -> SocketType -> IO SockID;
_prim_connect : SockID -> SockAddr -> IO Int;
_prim_bind    : SockID -> SockAddr -> IO Int;
_prim_listen  : SockID -> Int -> IO Int;
_prim_accept  : SockID -> IO (SockID & SockAddr);

_prim_sendTo  : SockID -> RawPacket -> SockAddr -> IO Int;
_prim_send    : SockID -> RawPacket -> IO Int;

_prim_recvFrom : SockID -> IO (RawPacket & SockAddr);
_prim_recv     : SockID -> IO RawPacket;

_prim_close    : SockID -> IO ();
_prim_shutdown : SockID -> RW -> IO ();

------------ Implementation ------------

sockInt : SocketType -> Int;
sockInt Stream = 0;
sockInt Datagram = 1;

intSock : Int -> SocketType;
intSock 0 = Stream;
intSock 1 = Datagram;

famInt : Family -> Int;
famInt UNIX = 0;
famInt INET = 1;

intFam : Int -> Family;
intFam 0 = UNIX;
intFam 1 = INET;

validSockID : SockID -> Bool;
validSockID (MkSock s) = s >= 0;

validPacket : RawPacket -> Bool;
validPacket (RPkt p _) = not (isNull p);

f_socket = mkForeign (FFun "prim_socket" [FInt, FInt] FInt); [%eval]
f_connect = mkForeign (FFun "prim_connect" [FInt, FStr, FInt] FInt); [%eval]
f_bind = mkForeign (FFun "prim_bind" [FInt, FStr, FInt] FInt); [%eval]
f_bind_any = mkForeign (FFun "prim_bind_any" [FInt, FInt] FInt); [%eval]
f_listen = mkForeign (FFun "prim_listen" [FInt, FInt] FInt); [%eval]
f_accept = mkForeign (FFun "prim_accept" [FInt] (FAny (SockID & SockAddr))); [%eval]

f_sendTo = mkForeign (FFun "prim_sendTo" [FInt, FStr, FInt, FAny RawPacket] FInt); [%eval]
f_send = mkForeign (FFun "prim_send" [FInt, FAny RawPacket] FInt); [%eval]
f_recvFrom = mkForeign (FFun "prim_recvFrom" [FInt] (FAny (RawPacket & SockAddr))); [%eval]
f_recv = mkForeign (FFun "prim_recv" [FInt] (FAny RawPacket)); [%eval]

f_closesock = mkForeign (FFun "close" [FInt] FInt); [%eval]
f_shutdown = mkForeign (FFun "prim_shutdown" [FInt, FInt] FUnit); [%eval]

_prim_socket  : Family -> SocketType -> IO SockID;
_prim_socket fam ty = do { i <- f_socket (famInt fam) (sockInt ty);
                           return (MkSock i); };

_prim_connect : SockID -> SockAddr -> IO Int;
_prim_connect (MkSock s) (HostPort h p) = f_connect s h p;
_prim_connect (MkSock s) (Port p) = return (-1);

_prim_bind    : SockID -> SockAddr -> IO Int;
_prim_bind (MkSock s) (HostPort h p) = f_bind s h p;
_prim_bind (MkSock s) (Port p) = f_bind_any s p;

_prim_listen  : SockID -> Int -> IO Int;
_prim_listen (MkSock s) m = f_listen s m;

_prim_accept  : SockID -> IO (SockID & SockAddr);
_prim_accept (MkSock s) = f_accept s;

_prim_sendTo  : SockID -> RawPacket -> SockAddr -> IO Int;
_prim_sendTo (MkSock s) pkt (HostPort h p) = f_sendTo s h p pkt;
_prim_sendTo (MkSock s) pkt (Port p) = return (-1);

_prim_send    : SockID -> RawPacket -> IO Int;
_prim_send (MkSock s) pkt = f_send s pkt;

_prim_recvFrom : SockID -> IO (RawPacket & SockAddr);
_prim_recvFrom (MkSock s) = f_recvFrom s;

_prim_recv     : SockID -> IO RawPacket;
_prim_recv (MkSock s) = f_recv s;

_prim_close    : SockID -> IO ();
_prim_close (MkSock s) = do { f_closesock s; return II; };

_prim_shutdown : SockID -> RW -> IO ();
_prim_shutdown (MkSock s) Read  = f_shutdown s 0;
_prim_shutdown (MkSock s) Write = f_shutdown s 1;
