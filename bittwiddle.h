#ifndef _BITTWIDDLE_H
#define _BITTWIDDLE_H

#include <stdint.h>
#include <closure.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

typedef uint32_t word32;

///////// Packet data

typedef word32* PACKET;

PACKET newPacket(int length);
void dumpPacket(PACKET p, int length);

void setPacketByte(PACKET p, int b, int data);
void setPacketBits(PACKET p, int start, int end, int data);

void setPacketString(PACKET p, int start, char* string, int l, char t);

int getPacketByte(PACKET p, int b);
int getPacketBits(PACKET p, int start, int end);

//// Code for sending packets across a wire

// Anything waiting on a socket?
int isReadable(int sd, int timeOut);

typedef struct {
    int sock;
    struct sockaddr_in addr;
} Connection;

typedef struct {
    VAL buf;
    unsigned port;
    char* server;
} Recv;

// Open sockets
void* net_UDP_serverSocket(int port);
void* net_UDP_clientSocket(char* server, int port);
void* net_TCP_socket(char* server, int port);
void* net_TCP_listen(int port, int maxcon);
void* net_TCP_accept(void* s_in);
void  net_closeSocket(void* s);

int net_sendUDP(void* conn, char* server, int port, VAL stuff);
void* net_recvUDP(void* conn);

int net_sendTCP(void* conn, VAL stuff);
void* net_recvTCP(void* conn);

VAL get_recvPacket(void* recv);
char* get_recvServer(void* recv);
int get_recvPort(void* recv);

int nullPtr(void *ptr);

#endif
