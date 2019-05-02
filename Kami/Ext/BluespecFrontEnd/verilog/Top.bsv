import Vector::*;
import BuildVector::*;
import FIFO::*;
import GetPut::*;

import Proc::*;
import FRAM::*;

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
    Reg#(Bool) pgmInitOn <- mkReg(True);
    Reg#(Bit#(32)) pgmInitBase <- mkReg(unpack(0));
    Reg#(Bit#(5)) pgmInitOfs <- mkReg(unpack(0));
   
    FIFO#(MemRq) rqs <- mkFIFO();
    FIFO#(MemRs) rss <- mkFIFO();

    rule pgmInitRq;
        when (pgmInitOn, noAction);
        let rq = MemRq { addr: pgmInitBase + (zeroExtend(pgmInitOfs) << 2),
	                 op: False,
			 data: 0 };
        rqs.enq(rq);
	pgmInitOfs <= pgmInitOfs + 1;
	if (~pgmInitOfs == 0) begin
            pgmInitOn <= False;
	end
    endrule
    
    function ActionValue#(Bit#(32)) procPgmInit ();
        return (actionvalue 
                    rss.deq;
		    let ld = rss.first.data;
		    // return {ld[7:0], ld[15:8], ld[23:16], ld[31:24]};
		    return ld;
                endactionvalue);
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

(* synthesize *)
module mkTopM ();
    ForDRAM top <- mkTop ();
    FRAM fram <- mkFRAM ();

    rule doMem;
        let rq <- top.obtain_rq.get();
	if (rq.op) begin
	    $display ("Handling a store: addr: %d, data: %d", rq.addr, rq.data);
	    fram.store((rq.addr) >> 2, rq.data);
            top.send_rs.put(MemRs {data: 0});
        end else begin
	    $display ("Handling a load: addr: %d", rq.addr);
	    let rs <- fram.load((rq.addr) >> 2);
	    top.send_rs.put(MemRs {data: rs});
	end
    endrule

endmodule: mkTopM

