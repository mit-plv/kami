import Vector::*;
import BuildVector::*;

import Proc::*;

interface FrontEnd;
    method Action toHost_a (Bit#(32) val);
    method Action toHost_aa (Bit#(32) val);
endinterface

module mkFrontEnd (FrontEnd);
  
    method Action toHost_a (Bit#(32) val);
    	$display ("Got the message: (%d, 1)\n", val);
    endmethod

    method Action toHost_aa (Bit#(32) val);
    	$display ("Got the message: (%d, 2)\n", val);
    endmethod

endmodule

(* synthesize *)
module mkHost (Empty);
    FrontEnd frontEnd <- mkFrontEnd ();
    Empty proc <- mkTop (frontEnd.toHost_aa, frontEnd.toHost_a);
endmodule

