import Vector::*;
import RegFile::*;

interface FRAM;
    method ActionValue#(Bit#(32)) load (Bit#(32) addr);
    method Action store (Bit#(32) addr, Vector#(4, Bool) byteEn, Bit#(32) data);
endinterface

module mkFRAM (FRAM);
    RegFile#(Bit#(10), Bit#(32)) fram <- mkRegFileFullLoad("fram_data.hex");

    function Bit#(32) upd_data(Bit#(32) oldData, Vector#(4, Bool) byteEn, Bit#(32) newData);
        Bit#(32) updData = {byteEn[3] ? newData[31:24] : oldData[31:24],
	                    byteEn[2] ? newData[23:16] : oldData[23:16],
			    byteEn[1] ? newData[15:8] : oldData[15:8],
			    byteEn[0] ? newData[7:0] : oldData[7:0]};
	return updData;
    endfunction

    method ActionValue#(Bit#(32)) load (Bit#(32) addr);
        Bit#(32) data = fram.sub(truncate(addr));
	return data;
    endmethod

    method Action store (Bit#(32) addr, Vector#(4, Bool) byteEn, Bit#(32) data);
        Bit#(32) oldData = fram.sub(truncate(addr));
	Bit#(32) updData = upd_data(oldData, byteEn, data);
        fram.upd(truncate(addr), updData);
    endmethod

endmodule : mkFRAM

