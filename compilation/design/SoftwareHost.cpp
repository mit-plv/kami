#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include "HostIndication.h"
#include "HostRequest.h"
#include "GeneratedTypes.h"

class HostIndication : public HostIndicationWrapper
{
public:
	virtual void msg_to_host1(uint32_t v) {
		printf("Got the message: (%d, 1)\n", v);
	}

	virtual void msg_to_host2(uint32_t v) {
		printf("Got the message: (%d, 2)\n", v);
	}

	virtual void msg_to_host3(uint32_t v) {
		printf("Got the message: (%d, 3)\n", v);
	}

	virtual void msg_to_host4(uint32_t v) {
		printf("Got the message: (%d, 4)\n", v);
	}

	HostIndication(unsigned int id) : HostIndicationWrapper(id) {}
};

int main(int argc, const char **argv) {
	
	HostIndication toHostIndication(IfcNames_HostIndicationH2S);
	HostRequestProxy* hostRequestProxy = new HostRequestProxy(IfcNames_HostRequestS2H);

	// Wait for some seconds from connectal to be ready
	usleep(3 * 1000);

	hostRequestProxy->start();	

	// busy-waiting
	while (1) {
	}

	return 0;
}
