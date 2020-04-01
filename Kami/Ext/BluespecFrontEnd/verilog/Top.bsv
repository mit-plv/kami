import Vector::*;
import BuildVector::*;
import FIFO::*;
import GetPut::*;

import Proc::*;
import FRAM::*;

typedef Struct1 MemRq;
typedef Struct2 MemRs;

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

    function Action procRq (MemRq rq);
        return (action 
	    rqs.enq(rq); 
	endaction);
    endfunction

    function ActionValue#(MemRs) procRs ();
        return (actionvalue
	            rss.deq;
		    return rss.first;
	        endactionvalue);
    endfunction

    Empty proc <- mkProc (procRs, procRq);

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

(* synthesize *)
module mkTopM ();
    ForDRAM top <- mkTop ();
    FRAM fram <- mkFRAM ();

    rule doMem;
        let rq <- top.obtain_rq.get();
	if (rq.op) begin
	    $display ("Handling a store");
	    fram.store((rq.addr) >> 2, rq.byteEn, rq.data);
            top.send_rs.put(MemRs {data: 0});
        end else begin
	    $display ("Handling a load");
	    let rs <- fram.load((rq.addr) >> 2);
	    top.send_rs.put(MemRs {data: rs});
	end
    endrule

endmodule: mkTopM

