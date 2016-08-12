#include <errno.h>
#include <stdio.h>
#include "HostIndication.h"
#include "GeneratedTypes.h"

class HostIndication : public HostIndicationWrapper
{
public:
	virtual void msg_to_host(uint32_t v, uint32_t pid) {
		printf("Got the message: (%d, %d)\n", v, pid);
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
