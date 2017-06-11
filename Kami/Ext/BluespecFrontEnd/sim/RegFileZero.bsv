package RegFileZero;

import RegFile::*;

module mkRegFileFullZero(RegFile#(a, t)) provisos (Bounded#(a), Bits#(a, aSz), Bits#(t, tSz));
    (* hide *)
    RegFile#(a, t) _m <- mkRegFileFull;
    Reg#(Bool) init <- mkReg(False);
    Reg#(Bit#(aSz)) initIndex <- mkReg(0);
    Bit#(aSz) nextInitIndex = initIndex + 1;
    rule doRegFileInit(!init);
        _m.upd(unpack(initIndex), unpack(0));
        initIndex <= initIndex + 1;
        if (initIndex == '1) init <= True;
    endrule
    method t sub(a i) if (init);
        return _m.sub(i);
    endmethod
    method Action upd(a i, t d) if (init);
        _m.upd(i,d);
    endmethod
endmodule

endpackage
