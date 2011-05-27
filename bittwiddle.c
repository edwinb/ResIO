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

#include <bittwiddle.h>
#include <closure.h>

PACKET newPacket(int length) {
    int words = length >> 5;
    if ((length & 31)!=0) words++; // Need one more if it's not exactly aligned
//    printf("%d words\n", words);
    PACKET p = EMALLOC(words*sizeof(word32));
    memset(p, words*sizeof(word32), 0);
    return p;
}

void dump_binary(int x)
{
    unsigned int z, i;
    for (z = 1 << 31, i=1; z > 0; z >>= 1, i++)
    {
        putchar(((x & z) == z) ? '1' : '0');
	if (i%8==0) putchar(' ');
    }
}

void dumpPacket(PACKET p, int length) {
    int i;
    int words = length >> 5;
    if ((length & 31)!=0) words++; // Need one more if it's not exactly aligned

    for (i=0; i<words; ++i) {
	printf("%x      \t", p[i]);
	dump_binary(p[i]);
	printf("\n");
    }
    printf("\n");
}

word32 setnbits(word32 v, int startoff, int endoff, int data) {
//    printf("Setting %d, %d to %d\n", startoff, endoff, data);
//    printf("%x\n", v);
    // Clear the bits in v from startoff to endoff.
    word32 two_m = (0xffffffff << (32-startoff)) ^ 0xffffffff;
    word32 two_n = (0xffffffff << (32-endoff)) ^ 0xffffffff;

    // Right, (two_m - two_n) is now ones in the position we want to clear.
    // So, flip it, to make it zeros we want to clear, ones elsewhere,
    // then AND v with it to pick out the bits we want to keep.

    v = v & ((two_m - two_n) ^ 0xffffffff);

    // Put the data in the right place (from startbit to endbit, all other
    // bits zero).
    word32 nv = data << (32-endoff);

//    printf("%x\n", nv);
//    printf("%x\n", v | nv);

    // Put nv in the right place in v.
    return (v | nv);
}



word32 getnbits(word32 v, int startbit, int endbit) {
//    printf("Getting %d, %d\n", startbit, endbit);
    return (v << startbit) >> (startbit + (32-endbit));
}

void setPacketByte(PACKET p, int b, int data) {
    p[b] = data;
}

void setPacketBits(PACKET p, int start, int end, int data) {
    int startb = start >> 5; // Word the start bits are in
    int endb = end >> 5;     // Word the end bits are in

    int startoff = start & 31; // Offset of start bits in that word
    int endoff = (end & 31)+1; // Offset of end bits in that word

    if (startb==endb) { // In the same word, easy...
	p[startb] = setnbits(p[startb], startoff, endoff, data);
    } else {
	// Set the least significant 32-[startoff] bits of p[startb] to
	// [data] >> [endoff].
	p[startb] = setnbits(p[startb], startoff, 32, data >> endoff);

	// Set the most significant [endoff] bits of p[endb] to the least
	// significant [endoff] bits of [data].
	p[endb] = setnbits(p[endb], 0, endoff, 
			   (data << (32 - endoff)) >> (32 - endoff));
    }
}

void setPacketString(PACKET p, int start, char* s, int l, char t) {
    int i;
    while(*s!=t && (l!=0)) {
	setPacketBits(p, start, start+7, (int)(*s));
	start+=8;
	++s;
	--l;
    }
}

int getPacketByte(PACKET p, int b) {
    return p[b];
}

int getPacketBits(PACKET p, int start, int end) {
    int startb = start >> 5; // Word the start bits are in
    int endb = end >> 5;     // Word the end bits are in

    int startoff = start & 31; // Offset of start bits in that word
    int endoff = 1 + (end & 31); // Offset of end bits in that word
    int rv;

    if (startb==endb) {
	rv = getnbits(p[startb], startoff, endoff);
    } else {
	int startn = getnbits(p[startb], startoff, 32);
	int endn = getnbits(p[endb], 0, endoff);
	rv = (startn << endoff) + endn; 
    }
//    printf("%d to %d is %d\n", start, end, rv);
    return rv;
}

// Now some network code

int isReadable(int sd, int timeOut) { // milliseconds
    fd_set socketReadSet;
    FD_ZERO(&socketReadSet);
    FD_SET(sd,&socketReadSet);
    struct timeval tv;
    if (timeOut) {
	tv.tv_sec  = timeOut / 1000;
	tv.tv_usec = (timeOut % 1000) * 1000;
    } else {
	tv.tv_sec  = 0;
	tv.tv_usec = 0;
    } // if
    if (select(sd+1,&socketReadSet,0,0,&tv) == -1) {
	printf("READ ERROR!\n");
	return 0;
    } // if
    return FD_ISSET(sd,&socketReadSet) != 0;
} /* isReadable */

void* net_UDP_clientSocket(char* server, int port) {
    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int s;
    struct sockaddr_in si_me, si_other;

    if ((s=socket(AF_INET, SOCK_DGRAM, 0))==-1) {
	printf("FAIL 1\n");
	return NULL;
    }

    memset((char *) &si_other, 0, sizeof(si_other));
    si_other.sin_family = AF_INET;
    si_other.sin_port = htons(port);

    if (inet_aton(server, &si_other.sin_addr)==0) {
	printf("FAIL 2\n");
	return NULL;
    }

    // Bind, so we can receive replies.
    si_me.sin_family = AF_INET;
    si_me.sin_port = htons(0);
    si_me.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me))<0) {
	return NULL;
    }

    con->sock = s;
    con->addr = si_other;

//    printf("Opened client socket %d\n", s);
    return con;
}

void* net_UDP_serverSocket(int port) {
    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int s;
    struct sockaddr_in si_me;

    if ((s=socket(AF_INET, SOCK_DGRAM, 0))==-1) {
	return NULL;
    }

    memset((char *) &si_me, 0, sizeof(si_me));
    si_me.sin_family = AF_INET;
    si_me.sin_port = htons(port);
    si_me.sin_addr.s_addr = htonl(INADDR_ANY);
    if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me))==-1) {
	return NULL;
    }

    con->sock = s;
    con->addr = si_me;

//    printf("Opened server socket %d\n", s);
    return con;
}

void* net_TCP_socket(char* server, int port) {
    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int s;
    struct sockaddr_in addr;
    struct hostent *hostinfo;

    if ((s=socket(AF_INET, SOCK_STREAM, 0))==-1) {
	printf("FAIL 1\n");
	return NULL;
    }

    hostinfo = gethostbyname(server);
    if (hostinfo == NULL) {
	printf("FAIL 2\n");
	return NULL;
    }
    addr.sin_family = AF_INET;
    addr.sin_addr = *(struct in_addr *)hostinfo->h_addr;
    addr.sin_port = htons(port);

    if (connect(s, (struct sockaddr *)(&addr),
		sizeof(struct sockaddr_in)) == -1) {
	printf("FAIL 3 %s\n", strerror(errno));
	return NULL;
    }

    con->sock = s;
    con->addr = addr;

//    printf("Opened client socket %d\n", s);
    return con;
}

void* net_TCP_listen(int port, int maxcon)
{
    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int sock;
    struct sockaddr_in name;

    sock = socket(PF_INET, SOCK_STREAM, getprotobyname("tcp")->p_proto);
    name.sin_family = AF_INET;

/*    int val = 1;
    setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &val, sizeof(int));
    fcntl(sock, F_SETFL, O_NONBLOCK);
*/

    name.sin_port = htons(port);
    name.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(sock, (struct sockaddr *)(&name), sizeof(struct sockaddr_in))) {
	printf("BIND FAIL\n");
        return NULL;
    }
    if (listen(sock, maxcon)) {
	printf("LISTEN FAIL\n");
	return NULL;
    }

    con->sock = sock;
    con->addr = name;
    return con;
}

void* net_TCP_accept(void* s_in) {
    Connection* con_in = (Connection*)s_in;
    Connection* con = (Connection*)EMALLOC(sizeof(Connection));

    struct sockaddr_in addr;
    socklen_t len = sizeof(struct sockaddr_in);

    int client = accept(con_in->sock, (struct sockaddr*)&addr, &len);
    if (client==-1) {
	printf("ACCEPT FAIL\n");
	return NULL;
    }
    
    con->sock = client;
    con->addr = addr;
    return (void*)con;
}

void net_closeSocket(void* s) {
    close(((Connection*)s)->sock);
}


int net_sendUDP(void* conn, char* server, int port, VAL stuff) {
    VAL pkt = GETPTR(PROJECT(stuff,0));
    int len = GETINT(PROJECT(stuff,1));
    int words = len >> 5;
    if ((len & 31)!=0) ++words;

    Connection* c = (Connection*)conn;
    int s = c->sock;
    struct sockaddr_in other = c->addr;
    memset((char *) &other, 0, sizeof(other));
    other.sin_family = AF_INET;
    other.sin_port = htons(port);
    if (inet_aton(server, &other.sin_addr)==0) {
	return -1;
    }

    if (sendto(s, pkt, words*sizeof(word32), 0, (struct sockaddr*)&other, 
	       sizeof(other))==-1) {
	return -1;
    }
    return 0;
}

void* net_recvUDP(void* conn) {
    struct sockaddr_in other;
    Connection* c = (Connection*)conn;
    int s = c->sock;
    socklen_t slen = sizeof(other);
    struct sockaddr_in me = c->addr;

    // TMP HACK: 512 should be enough for the purposes of this experiment...
    // Do it properly some time.
    word32* buf = (word32*)EMALLOC(512*sizeof(word32));

//    printf("Waiting to receive\n");

    int error;
//    while (!isReadable(s,100)) printf(".\n");

    if (!isReadable(s, 1000)) {
	printf("Nothing\n");
	return NULL;
    }

    int recvlen = recvfrom(s, buf, 512*sizeof(word32), 0, (struct sockaddr *)&other, &slen);

    if (recvlen==-1) {
	return NULL;
    } 

    printf("Received %d bytes from %s:UDP%u\n", 
	   recvlen,inet_ntoa(other.sin_addr),
	   ntohs(other.sin_port));

    Recv* r = (Recv*)EMALLOC(sizeof(Recv));
    r->buf = CONSTRUCTOR2(0, MKPTR(buf), MKINT(recvlen << 3));
    r->server = inet_ntoa(other.sin_addr);
    r->port = ntohs(other.sin_port);

    return (void*)r;
}

int net_sendTCP(void* conn, VAL stuff) {
    VAL pkt = GETPTR(PROJECT(stuff,0));
    int len = GETINT(PROJECT(stuff,1));
    int words = len >> 5;
    if ((len & 31)!=0) ++words;

    Connection* c = (Connection*)conn;
    int s = c->sock;

    if (send(s, pkt, words*sizeof(word32), 0)==-1) {
	return -1;
    }
    return 0;
}

void* net_recvTCP(void* conn) {
    Connection* c = (Connection*)conn;
    int s = c->sock;
    struct sockaddr_in me = c->addr;

    // TMP HACK: 512 should be enough for the purposes of this experiment...
    // Do it properly some time.
    word32* buf = (word32*)EMALLOC(512*sizeof(word32));

//    printf("Waiting to receive\n");

    int error;
//    while (!isReadable(s,100)) printf(".\n");

    if (!isReadable(s, 1000)) {
	printf("Nothing\n");
	return NULL;
    }

    int recvlen = recv(s, buf, 512*sizeof(word32), 0);

    if (recvlen==-1) {
	return NULL;
    } 

    printf("Received %d bytes from %s:%u\n", 
	   recvlen,inet_ntoa(me.sin_addr),
	   ntohs(me.sin_port));

    Recv* r = (Recv*)EMALLOC(sizeof(Recv));
    r->buf = CONSTRUCTOR2(0, MKPTR(buf), MKINT(recvlen << 3));
    r->server = inet_ntoa(me.sin_addr);
    r->port = ntohs(me.sin_port);

    return (void*)r;
}


VAL get_recvBuf(void* recv) {
    return ((Recv*)recv)->buf;
}

char* get_recvServer(void* recv) {
    return ((Recv*)recv)->server;
}

int get_recvPort(void* recv) {
    return ((Recv*)recv)->port;
}

int nullPtr(void *ptr) {
    return ptr==NULL;
}

