import RegFile::*;

interface Bram#(type sz, type t);
  method Action readRq(sz idx);
  method t readRs();
  method Action write(sz idx, t d);
endinterface

module mkBram(Bram#(sz, t)) provisos (Bounded#(sz), Bits#(sz, szb), Bits#(t, tb));
  RegFile#(sz, t) rf <- mkRegFileFullLoad("file.hex");
  Reg#(t) data <- mkRegU;

  method Action readRq(sz idx);
    data <= rf.sub(idx);
  endmethod

  method t readRs();
    return data;
  endmethod

  method Action write(sz idx, t d);
    rf.upd(idx, d);
  endmethod
endmodule

(* synthesize *)
module mkBramInst(Bram#(Bit#(10), Bit#(32)));
  let bram <- mkBram;
  return bram;
endmodule
