#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/timerfd.h>
#include <net/if.h>
#include <netinet/ip.h>
#include <net/route.h>
#include <poll.h>
#include <assert.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include <limits.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>

#define elem(x) ((int)(sizeof(x)/sizeof(x[0])))
#define IP(a,b,c,d) (u8[4]){a,b,c,d}
#define MIN(a,b) (((a)<(b))?(a):(b))

enum{
	IPv4addrlen = 4,
	Maxoptlen = 312-4,
	Maxfilelen = 128,
	Maxhwlen = 16,

	SrcPort = 68,
	DstPort = 67,

	Discover = 1,
	Offer = 2,
	Request = 3,
	DHCPdecline = 4,
	Ack = 5,
	Nak = 6,
	Release = 7,

	Timeout0 = 200,
	Timeout1,
	Timeout2,

	Bootrequest = 1,
	// boot flags
	Fbroadcast	= 0x8000,

	Broadcast = 0,
	Unicast = 1,

	// bootp option type 
	OBpad = 0,
	OBmask = 1,
	OBtimeoff = 2,
	OBrouter = 3,
	OBdnsserver = 6,
	OBhostname = 12,
	OBend = 255,
	
	// dhcp v4 options
	ODipaddr = 50,
	ODlease = 51,
	ODtype = 53,
	ODserverid = 54,
	ODrenewaltime = 58,
	ODrebindingtime = 59,
	ODclientid = 61,
};

typedef uint8_t u8;
typedef uint32_t u32;
typedef uint64_t u64;
typedef struct Bootp {
	u8 op[1];
	u8 htype[1]; // hardware type
	u8 hlen[1];  // hardware addr len
	u8 hops[1];
	u8 xid[4];      //random number
	u8 secs[2];
	u8 flags[2];
	u8 ciaddr[IPv4addrlen]; // client ip addr (client tells server)
	u8 yiaddr[IPv4addrlen]; // client ip addr (server tells client)
	u8 siaddr[IPv4addrlen]; // server ip addr 
	u8 giaddr[IPv4addrlen]; // gateway ip addr
	u8 chaddr[Maxhwlen]; // client hw address
	u8 sname[64]; // server host name
	u8 file[Maxfilelen]; // boot file name
	u8 optmagic[4]; 
	u8 optdata [Maxoptlen];
} Bootp;

static Bootp bp;
static time_t begat;
static u8 optmagic[] = {99, 130, 83, 99};
static u8 client[IPv4addrlen];
static u8 server[IPv4addrlen];
static u8 mask[IPv4addrlen];
static u8 router[IPv4addrlen];
static u8 dns[IPv4addrlen];
static u64 xid;
static u8 hostname[HOST_NAME_MAX + 1];
static u8 hwaddr[sizeof(struct sockaddr) + 1];
static u8 cid[sizeof(struct sockaddr) + 1];
static char *ifname;
static int sock, timers[3];
static struct itimerspec timeout; // time to timeout - seconds

static void dhcpsend(int type, int how);

static void
cexit(int _)
{
	dhcpsend(Release, Unicast);
	close(sock);
	printf("bye\n");
	exit(0);
}

static void
put(u8 *dst, u32 src, int n)
{
	for(int i = 0; n--; ++i){
		dst[i] = (src >> (n * 8)) & 0xFF;
	}
}

static struct sockaddr*
iptoaddr(struct sockaddr *ifaddr, u8 ip[4], int port)
{
	struct sockaddr_in *in = (struct sockaddr_in*)ifaddr;
	in->sin_family = AF_INET;
	in->sin_port = htons(port);
	memcpy(&in->sin_addr, ip, sizeof(in->sin_addr));
	return ifaddr;
}

static void
optget(Bootp *bp, void *v, int opt, int n)
{
	u8 *p = bp->optdata;
	u8 *top = ((u8*)bp) + sizeof(*bp);
	while(p < top){
		int code = *p++;
		if(code == OBpad)
			continue;
		if(code == OBend || p == top)
			break;
		int len = *p++;
		if(len > top - p)
			break;
		if(code == opt){
			memcpy(v, p, MIN(len, n));
			break;
		}
		p += len;
	}
}

static u8*
optpput(u8 *p, int opt, u8 *v, int len)
{
	*p++ = opt;
	*p++ == (u8)len;
	memcpy(p, v, len);
	return p + len;
}

static u8*
optput(u8 *p, int opt, u32 v, int len)
{
	*p++ = opt;
	*p++ == (u8)len;
	put(p, v, len);
	return p + len;
}

static u8*
termput(u8 *p)
{
	*p++ = OBend;
	return p;
}

// make udp paylad
static int
udpsend(u8 ip[4], int fd, void *v, int n)
{
	struct sockaddr addr = {0};
	socklen_t addrlen = sizeof(addr);
	int wc = -1;

	iptoaddr(&addr, ip, DstPort);
	wc = sendto(fd, v, n, 0, &addr, addrlen);
	assert(wc != -1);
	return wc;
}

static int
udprecv(u8 ip[4], int fd, void *v, int n)
{
	struct sockaddr addr = {0};
	socklen_t addrlen = sizeof(addr);
	int rc = -1;

	iptoaddr(&addr, ip, SrcPort);
	rc = recvfrom(fd, v, n, 0, &addr, &addrlen);
	assert(rc != -1);
	return rc;
}

// make dhcp payload
static void
dhcpsend(int type, int how)
{
	u8 *ip, *p;

	memset(&bp, 0, sizeof(bp));
	put(bp.op, Bootrequest, 1);
	put(bp.htype, 1, 1);
	put(bp.hlen, 6, 1);
	memcpy(bp.xid, &xid, sizeof(xid));
	put(bp.secs, time(0) - begat, sizeof(bp.secs));
	put(bp.flags, Fbroadcast, sizeof(bp.flags));
	memcpy(bp.optmagic, optmagic, sizeof(bp.optmagic));
	memcpy(bp.chaddr, hwaddr, sizeof(bp.chaddr));
	p = bp.optdata;
	p = optput(p, ODtype, type, 1);
	p = optpput(p, ODclientid, cid, sizeof(cid));
	p = optpput(p, OBhostname, hostname, strlen(hostname));

	switch(type){
	case Discover:
		break;
	case Request:
	case Release:
		memcpy(bp.ciaddr,  client, sizeof(client));
		p = optpput(p, ODipaddr, client, sizeof(client));
		p = optpput(p, ODserverid, server, sizeof(server));
		break;
	default:
		assert(0);
	}

	p = termput(p);
	if(how == Broadcast) ip = IP(255,255,255,255);
	else ip = server;
	udpsend(ip, sock, &bp, p - (u8*)&bp);
}

static int
dhcprecv(void)
{
	struct pollfd pfd[] = {
		{.fd=sock, .events=POLL_IN},
		{.fd=timers[0], .events=POLL_IN},
		{.fd=timers[1], .events=POLL_IN},
		{.fd=timers[2], .events=POLL_IN}};
	
	u8 type = 0;
	assert(poll(pfd, elem(pfd), -1) != -1);
	if(pfd[0].revents){
		memset(&bp, 0, sizeof(bp));
		udprecv(IP(255,255,255,255), sock, &bp, sizeof(bp));
		optget(&bp, &type, ODtype, sizeof(type));
		return type;
	}
	u64 n = 0;
	if(pfd[1].revents){
		type = Timeout0;
		read(timers[0], &n, sizeof(n));
	}
	if(pfd[2].revents){
		type = Timeout1;
		read(timers[0], &n, sizeof(n));
	}
	if(pfd[3].revents){
		type = Timeout2;
		read(timers[2], &n, sizeof(n));
	};
	return type;
}

static void
settimeout(int i, u32 t)
{
	timeout.it_value.tv_sec = t;
	assert(timerfd_settime(timers[i], 0, &timeout, 0) >= 0);
}

static void
setdifftime(int i)
{
	assert(timerfd_gettime(timers[i], &timeout) >= 0);
	timeout.it_value.tv_nsec /= 2;
	if(timeout.it_value.tv_sec % 2)
		timeout.it_value.tv_nsec += 500000000;
	timeout.it_value.tv_sec /= 2;
	if(timeout.it_value.tv_sec < 60){
		timeout.it_value.tv_sec = 60;
		timeout.it_value.tv_nsec = 0;

	}
}

static void
setdns(u8 dns[4])
{
	char buf[1024];
	int fd;

	assert((fd = open("/etc/resolv.conf",O_CREAT|O_RDWR, 0644)) != -1);
	int wc = snprintf(buf, sizeof(buf)-1, "\nnameserver %u.%u.%u.%u\n",
		dns[0],dns[1],dns[2],dns[3]);
	assert(wc != -1);
	assert(wc == write(fd, buf, wc));
	close(fd);
}

static void
setip(u8 ip[4], u8 mask[4], u8 gw[4])
{
	struct ifreq  i = {0};
	struct rtentry r = {0}; // routing table
	int fd = -1;
	assert((fd = socket(PF_INET, SOCK_DGRAM, IPPROTO_IP)) != -1);

	strlcpy(i.ifr_name, ifname, IF_NAMESIZE);
	iptoaddr(&i.ifr_addr, ip, 0);
	ioctl(fd, SIOCSIFADDR, &i);
	iptoaddr(&i.ifr_netmask, mask, 0);
	ioctl(fd, SIOCSIFNETMASK, &i);
	i.ifr_flags = IFF_UP | IFF_RUNNING | IFF_BROADCAST | IFF_MULTICAST;
	ioctl(fd, SIOCSIFFLAGS, &i);
	r.rt_flags = RTF_UP | RTF_GATEWAY;
	iptoaddr(&r.rt_gateway, gw, 0);
	iptoaddr(&r.rt_genmask, IP(0,0,0,0), 0);
	iptoaddr(&r.rt_dst, IP(0,0,0,0), 0);
	ioctl(fd, SIOCADDRT, &r);

	close(fd);
}

static void
acceptlease(void)
{
	setip(client, mask, router);
	setdns(dns);
}

static void
run(void)
{
	u32 renewaltime, rebindtime, lease;

Init:
	dhcpsend(Discover, Broadcast);	
	settimeout(0, 1);

	for(;;)
	switch(dhcprecv()){
	case Offer:
		memcpy(client, bp.yiaddr, sizeof(client));
		optget(&bp, server, ODserverid, sizeof(server));
		goto Requesting;
	case Timeout0: goto Init;
	default: assert(0);
	}
Requesting:
	for(int t = 0; t < 5; ++t){
		dhcpsend(Request, Broadcast);
		settimeout(0, 4);
		switch(dhcprecv()){
		case Ack: goto Bound;
		case Nak: goto Init;
		case Timeout0: break;
		default: assert(0);
		}
	}
	fprintf(stderr, "timeout\n");
	cexit(1);
Bound:
	optget(&bp, mask, OBmask, sizeof(mask));
	optget(&bp, router, OBrouter, sizeof(router));
	optget(&bp, dns, OBdnsserver, sizeof(dns));
	optget(&bp, &renewaltime, ODrenewaltime, sizeof(renewaltime));
	optget(&bp, &lease, ODlease, sizeof(lease));
	renewaltime = ntohl(renewaltime);
	rebindtime = ntohl(rebindtime);	
	lease = ntohl(lease);
	acceptlease();
	printf("success lease\n");
	settimeout(0, renewaltime);
	settimeout(1, rebindtime);
	settimeout(2, lease);
	for(;;)
	switch(dhcprecv()){
	case Timeout0: goto Renewing;
	case Timeout1: goto Rebinding;
	case Timeout2: goto Init;
	}
Renewing:
	dhcpsend(Request, Unicast);
	setdifftime(1);
	settimeout(0, timeout.it_value.tv_sec);
	for(;;)
	switch(dhcprecv()){
	case Ack: goto Bound;
	case Timeout0: goto Renewing;
	case Timeout1: goto Rebinding;
	case Timeout2:
	case Nak: goto Init;
	default: assert(0);
	}
Rebinding:
	setdifftime(2);
	settimeout(0,timeout.it_value.tv_sec);
	dhcpsend(Request, Broadcast);
	for(;;)
	switch(dhcprecv()){
	case Ack: goto Bound;
	case Timeout0: goto Rebinding;
	case Timeout2:
	case Nak: goto Init;
	case Timeout1: break;
	default: assert(0);
	}
}

static void
dhcpinit(void)
{
	int fd = open("/dev/urandom", O_RDONLY);
	if(fd >= 0){
		read(fd, &xid, sizeof(xid));
		close(fd);
	}else
		xid =  time(0)*getpid();
	srand(xid);
}

static void
openlisten(void)
{
	int b = 1;
	struct ifreq r = {0};
	struct sockaddr a = {0};

	assert((sock = socket(AF_INET, SOCK_DGRAM, 0)) != -1);
	assert(setsockopt(sock, SOL_SOCKET, SO_BROADCAST, &b, sizeof(b)) != -1);
	strlcpy(r.ifr_name, ifname, IF_NAMESIZE);
	ioctl(sock, SIOCGIFINDEX, &r);
	assert(setsockopt(sock, SOL_SOCKET, SO_BINDTODEVICE, &r, sizeof(r)) != -1);
	iptoaddr(&a, IP(255,255,255,255), SrcPort);
	assert(bind(sock, &a, sizeof(a)) == 0);
	ioctl(sock, SIOCGIFHWADDR, &r);
	memcpy(hwaddr, r.ifr_hwaddr.sa_data, sizeof(r.ifr_hwaddr.sa_data));
	memcpy(cid, hwaddr, sizeof(cid));
}

int
main(int argc, char *argv[])
{
	if(argc == 2) ifname = argv[1];	
	else ifname = "wlp3s0";

	signal(SIGTERM, cexit);
	gethostname(hostname, sizeof(hostname));
	dhcpinit();
	openlisten();

	for(int i = 0; i < elem(timers); ++i)
		assert((timers[i]=timerfd_create(CLOCK_BOOTTIME, TFD_CLOEXEC)) != -1);
	begat = time(0);
	run();
	return 0;
}
