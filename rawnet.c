#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

#include <closure.h>
#include <rawnet.h>
#include <bittwiddle.h>

int  prim_socket(int family, int socktype) {
    int dom, ty;
    if (family==0) { dom = AF_UNIX; } else { dom = AF_INET; }
    if (socktype==0) { ty = SOCK_STREAM; } else { ty = SOCK_DGRAM; }
    
    return socket(dom, ty, 0);
}

int prim_connect(int socket, char* host, int port)
{
    struct sockaddr_in name;
    struct hostent *hostinfo;

    hostinfo = gethostbyname(host);
    if (hostinfo == NULL) {
	return -1;
    }

    name.sin_family = AF_INET;
    name.sin_port = htons(port);
    name.sin_addr = *(struct in_addr*)hostinfo->h_addr;

    return connect(socket, (struct sockaddr*)(&name), 
		   sizeof(struct sockaddr_in));
}

int prim_bind(int socket, char* host, int port)
{
    struct sockaddr_in name;
    struct hostent *hostinfo;

    hostinfo = gethostbyname(host);
    if (hostinfo == NULL) {
	return -1;
    }

    memset((char *) &name, 0, sizeof(name));
    name.sin_family = AF_INET;
    name.sin_port = htons(port);
    name.sin_addr = *(struct in_addr*)hostinfo->h_addr;

    return bind(socket, (struct sockaddr*)(&name), 
		sizeof(struct sockaddr_in));
}

int prim_bind_any(int socket, int port)
{
    struct sockaddr_in name;

    memset((char *) &name, 0, sizeof(name));
    name.sin_family = AF_INET;
    name.sin_port = htons(port);
    name.sin_addr.s_addr = htonl(INADDR_ANY);

    return bind(socket, (struct sockaddr*)(&name), 
		sizeof(name));
}

int prim_listen(int socket, int maxconn)
{
    return listen(socket, maxconn);
}

#define NOADDR (CONSTRUCTOR1(1, MKINT(0)))
#define EMPTYPKT (CONSTRUCTOR2(0, MKPTR(0), 0))

// VAL is (SockID & SockAddr)
VAL prim_accept(int socket)
{
    struct sockaddr_in addr;
    socklen_t len = sizeof(struct sockaddr_in);

    int sock = accept(socket, (struct sockaddr*)&addr, &len);
    VAL sockaddr;
    if (sock==-1) {
	sockaddr = NOADDR;
    } else {
	sockaddr = CONSTRUCTOR2(0, MKSTR(inet_ntoa(addr.sin_addr)), 
				MKINT(addr.sin_port));
    }

    return CONSTRUCTOR2(0, CONSTRUCTOR1(0, MKINT(sock)), sockaddr);
}

int prim_sendTo(int socket, char* host, int port, VAL stuff)
{
    VAL pkt = GETPTR(PROJECT(stuff,0));
    int len = GETINT(PROJECT(stuff,1));
    int words = len >> 5;
    if ((len & 31)!=0) ++words;

    struct sockaddr_in other;
    memset((char *) &other, 0, sizeof(other));

    other.sin_family = AF_INET;
    other.sin_port = htons(port);
    if (inet_aton(host, &other.sin_addr)==0) {
	return -1;
    }
    
    return sendto(socket, pkt, words*sizeof(uint32_t), 0, 
		  (struct sockaddr*)&other, sizeof(other));
}

// VAL is RawPacket
int prim_send(int socket, VAL stuff)
{
    VAL pkt = GETPTR(PROJECT(stuff,0));
    int len = GETINT(PROJECT(stuff,1));
    int words = len >> 5;
    if ((len & 31)!=0) ++words;

    return send(socket, pkt, words*sizeof(uint32_t), 0);
}

// VAL is (RawPacket & SockAddr)
VAL prim_recvFrom(int socket)
{
    struct sockaddr_in other;

    socklen_t slen = sizeof(other);

    // TMP HACK: 512 should be enough for the purposes of this experiment...
    // Do it properly some time.
    uint32_t* buf = (uint32_t*)EMALLOC(512*sizeof(uint32_t));

    if (!isReadable(socket, 10000)) {
	return CONSTRUCTOR2(0, EMPTYPKT, NOADDR);
    }
    int recvlen = recvfrom(socket, buf, 512*sizeof(uint32_t), 0,
			   (struct sockaddr*)&other, &slen);
    if (recvlen == -1) {
	return CONSTRUCTOR2(0, EMPTYPKT, NOADDR);
    }

    return CONSTRUCTOR2(0, 
			CONSTRUCTOR2(0, MKPTR(buf), MKINT(recvlen << 3)),
			CONSTRUCTOR2(0, MKSTR(inet_ntoa(other.sin_addr)),
				     MKINT(ntohs(other.sin_port))));
}

// VAL is RawPacket
VAL prim_recv(int socket)
{
    // TMP HACK: 512 should be enough for the purposes of this experiment...
    // Do it properly some time.
    uint32_t* buf = (uint32_t*)EMALLOC(512*sizeof(uint32_t));

    if (!isReadable(socket, 10000)) {
	return CONSTRUCTOR2(0, EMPTYPKT, NOADDR);
    }

    int recvlen = recv(socket, buf, 512*sizeof(word32), 0);

    if (recvlen==-1) {
	return CONSTRUCTOR2(0, EMPTYPKT, NOADDR);
    } 

    return CONSTRUCTOR2(0, MKPTR(buf), MKINT(recvlen << 3));
}

void prim_shutdown(int socket, int how)
{
    if (how==0) {
	shutdown(socket, SHUT_RD); 
    }
    else { 
	shutdown(socket, SHUT_WR); 
    }
}
