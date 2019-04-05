import Vector::*;
import BuildVector::*;
import FIFO::*;
import GetPut::*;

import Proc::*;

typedef Struct4 MemRq;
typedef Struct5 MemRs;

// DRAM can use this interface.
interface ForDRAM;
    interface Get#(MemRq) obtain_rq;
    interface Put#(MemRs) send_rs;
endinterface

// The top module, which includes the processor module,
// supports the ForDRAM interface.

(* synthesize *)
module mkTop (ForDRAM);

    FIFO#(MemRq) rqs <- mkFIFO();
    FIFO#(MemRs) rss <- mkFIFO();

    function ActionValue#(Bit#(32)) procPgmInit (Bit#(5) addr);
        return (actionvalue return 0; endactionvalue);
    endfunction

    function Action procRq (MemRq rq);
        return (action rqs.enq(rq); endaction);
    endfunction

    function ActionValue#(MemRs) procRs ();
        return (actionvalue
	            rss.deq;
		    return rss.first;
		endactionvalue);
    endfunction

    Empty proc <- mkProc (procPgmInit, procRs, procRq);

    interface obtain_rq = (interface Get;
        method ActionValue#(MemRq) get;
            rqs.deq;
            return rqs.first; 
        endmethod
    endinterface);

    interface send_rs = (interface Put;
	method Action put(MemRs data);
            rss.enq(data);
        endmethod
    endinterface);

endmodule: mkTop

