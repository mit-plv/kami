import Vector::*;
import BuildVector::*;

import Proc::*;

// Connectal interfaces

interface HostIndication;
    method Action msg_to_host1(Bit#(32) v);
    method Action msg_to_host2(Bit#(32) v);
endinterface

interface HostRequest;
    method Action start();
endinterface

// Connectal interfaces end

// A frontend wrapper to deal with the trigger from SW

interface FrontEnd;
    method Action toHost_a (Bit#(32) val);
    method Action toHost_aa (Bit#(32) val);
    method Action start ();
endinterface

module mkFrontEnd#(HostIndication indication) (FrontEnd);
  
    Reg#(Bool) ready <- mkReg(False);

    method Action toHost_a (Bit#(32) val);
        if (ready) begin
	    indication.msg_to_host1(val);
	end
    endmethod

    method Action toHost_aa (Bit#(32) val);
        if (ready) begin
	    indication.msg_to_host2(val);
	end
    endmethod

    method Action start();
        ready <= True;
    endmethod
endmodule

interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    FrontEnd frontEnd <- mkFrontEnd (indication);
    Empty proc <- mkTop (frontEnd.toHost_aa, frontEnd.toHost_a);

    interface HostRequest request;
        method Action start ();
	    frontEnd.start ();
	endmethod
    endinterface
endmodule

