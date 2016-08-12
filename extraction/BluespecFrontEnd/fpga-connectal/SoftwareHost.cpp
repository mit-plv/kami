#include <errno.h>
#include <stdio.h>
#include "HostIndication.h"
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

	HostIndication(unsigned int id) : HostIndicationWrapper(id) {}
};

int main(int argc, const char **argv) {
	HostIndication toHostIndication(IfcNames_HostIndicationH2S);

	// TODO: instantiate HostIndication with threading
	
	int v = 0;
	int ret = scanf("%d", &v);

	if (ret) {
		printf("succeed");
	}

	return v;
}
