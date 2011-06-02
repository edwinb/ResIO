#ifndef _RAWNET_H
#define _RAWNET_H

#include <stdint.h>
#include <closure.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

int prim_socket(int family, int socktype);
int prim_connect(int socket, char* host, int port);
int prim_bind(int socket, char* host, int port);
int prim_bind_any(int socket, int port);
int prim_listen(int socket, int maxconn);
// VAL is (Socket & SockAddr)
VAL prim_accept(int socket);

int prim_sendTo(int socket, char* host, int port, VAL stuff);
// VAL is RawPacket
int prim_send(int socket, VAL stuff);

// VAL is (RawPacket & SockAddr)
VAL prim_recvFrom(int socket);
// VAL is RawPacket
VAL prim_recv(int socket);

void prim_shutdown(int socket, int how);

#endif
