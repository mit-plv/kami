import RegFile::*;

interface FRAM;
    method ActionValue#(Bit#(32)) load (Bit#(32) addr);
    method Action store (Bit#(32) addr, Bit#(32) data);
endinterface

module mkFRAM (FRAM);
    RegFile#(Bit#(10), Bit#(32)) fram <- mkRegFileFullLoad("fram_data.hex");

    method ActionValue#(Bit#(32)) load (Bit#(32) addr);
        Bit#(32) data = fram.sub(truncate(addr));
	return data;
    endmethod

    method Action store (Bit#(32) addr, Bit#(32) data);
        fram.upd(truncate(addr), data);
    endmethod

endmodule : mkFRAM

