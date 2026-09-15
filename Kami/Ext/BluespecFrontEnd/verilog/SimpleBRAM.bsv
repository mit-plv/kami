package SimpleBRAM;

import RegFile::*;

// A block RAM with one read port and one write port. A read is requested
// with readRq and its result is available from readRs in the next cycle.
interface Bram#(type addrT, type dataT);
    method Action readRq (addrT idx);
    method dataT readRs ();
    method Action write (addrT idx, dataT d);
endinterface

module mkBram (Bram#(addrT, dataT))
    provisos (Bits#(addrT, addrSz), Bits#(dataT, dataSz), Bounded#(addrT));
    RegFile#(addrT, dataT) rf <- mkRegFileFull;
    Reg#(dataT) data <- mkRegU;

    method Action readRq (addrT idx);
        data <= rf.sub(idx);
    endmethod

    method dataT readRs ();
        return data;
    endmethod

    method Action write (addrT idx, dataT d);
        rf.upd(idx, d);
    endmethod
endmodule

(* synthesize *)
module mkBramInst (Bram#(Bit#(10), Bit#(32)));
    Bram#(Bit#(10), Bit#(32)) bram <- mkBram;
    return bram;
endmodule

endpackage
