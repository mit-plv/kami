CONNECTALDIR?=../connectal
S2H_INTERFACES = HostRequest:Host.request
H2S_INTERFACES = Host:HostIndication

BSVFILES= Host.bsv
CPPFILES= SoftwareHost.cpp

CONNECTALFLAGS+= --mainclockperiod=16
CONNECTALFLAGS+= --bscflags="+RTS -K100M -RTS -steps-max-intervals 10000000"

include $(CONNECTALDIR)/Makefile.connectal

