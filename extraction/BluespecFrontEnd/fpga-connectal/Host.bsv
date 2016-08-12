import Vector::*;
import BuildVector::*;

import Proc::*;

// Connectal interfaces

interface HostIndication;
    method Action msg_to_host1(Bit#(32) v);
    method Action msg_to_host2(Bit#(32) v);
endinterface

// Connectal interfaces end

interface FrontEnd;
    method Action toHost_a (Bit#(32) val);
    method Action toHost_aa (Bit#(32) val);
endinterface

interface Host;
endinterface

module mkFrontEnd#(HostIndication indication) (FrontEnd);
  
    method Action toHost_a (Bit#(32) val);
	indication.msg_to_host1(val);
    endmethod

    method Action toHost_aa (Bit#(32) val);
	indication.msg_to_host2(val);
    endmethod

endmodule

module mkHost#(HostIndication indication) (Host);
    FrontEnd frontEnd <- mkFrontEnd (indication);
    Empty proc <- mkTop (frontEnd.toHost_aa, frontEnd.toHost_a);
endmodule

