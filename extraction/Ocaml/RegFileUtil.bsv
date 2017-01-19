
// Copyright (c) 2016 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

package RegFileUtil;

import RegFile::*;

module mkRegFileFullGenWith#(function t initF(a i))(RegFile#(a, t)) provisos (Bounded#(a), Bits#(a, aSz), Bits#(t, tSz));
    (* hide *)
    RegFile#(a, t) _m <- mkRegFileFull;
    Reg#(Bool) init <- mkReg(False);
    Reg#(Bit#(aSz)) initIndex <- mkReg(0);
    Bit#(aSz) nextInitIndex = initIndex + 1;
    rule doRegFileInit(!init);
        _m.upd(unpack(initIndex), initF(unpack(initIndex)));
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

module mkRegFileFullReplicate#(t initVal)(RegFile#(a, t)) provisos (Bounded#(a), Bits#(a, aSz), Bits#(t, tSz));
    function t initF(a x);
        return initVal;
    endfunction
    (* hide *)
    let _m <- mkRegFileFullGenWith(initF);
    return _m;
endmodule

endpackage
