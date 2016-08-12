import Vector::*;
import BuildVector::*;

typedef struct { Bit#(7) opcode; Bit#(5) reg_; Bit#(4) addr; Bit#(32) value; Bit#(32) inst;  } Struct1 deriving(Eq, Bits);
typedef struct { Bit#(1) child; Struct6 rq;  } Struct10 deriving(Eq, Bits);
typedef struct { Bit#(1) child; Struct4 rs;  } Struct11 deriving(Eq, Bits);
typedef struct { Bit#(1) child; Struct7 msg;  } Struct12 deriving(Eq, Bits);
typedef struct { Bool valid; Bit#(1) value;  } Struct13 deriving(Eq, Bits);
typedef struct { Bit#(3) addr; Vector#(2, Bit#(2)) data;  } Struct14 deriving(Eq, Bits);
typedef struct { Bit#(3) addr; Vector#(2, Bit#(32)) data;  } Struct15 deriving(Eq, Bits);
typedef struct { Bit#(4) addr; Bool op; Bit#(32) data;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(32) data;  } Struct3 deriving(Eq, Bits);
typedef struct { Bit#(3) addr; Bit#(2) to; Vector#(2, Bit#(32)) line; Bool isVol;  } Struct4 deriving(Eq, Bits);
typedef struct { Bit#(2) addr; Bit#(2) data;  } Struct5 deriving(Eq, Bits);
typedef struct { Bit#(3) addr; Bit#(2) from; Bit#(2) to; Bit#(1) id;  } Struct6 deriving(Eq, Bits);
typedef struct { Bool isRq; Bit#(3) addr; Bit#(2) to; Vector#(2, Bit#(32)) line; Bit#(1) id;  } Struct7 deriving(Eq, Bits);
typedef struct { Bit#(2) addr; Bit#(1) data;  } Struct8 deriving(Eq, Bits);
typedef struct { Bit#(2) addr; Vector#(2, Bit#(32)) data;  } Struct9 deriving(Eq, Bits);

interface Module1;
    method Action enq_rqFromProc_aa (Struct2 x_0);
    method Action enq_rqFromProc_a (Struct2 x_0);
    method ActionValue#(Struct2) deq_rqFromProc_aa ();
    method ActionValue#(Struct2) deq_rqFromProc_a ();
    method ActionValue#(Struct2) firstElt_rqFromProc_aa ();
    method ActionValue#(Struct2) firstElt_rqFromProc_a ();
    method Action enq_rsToProc_aa (Struct3 x_0);
    method Action enq_rsToProc_a (Struct3 x_0);
    method ActionValue#(Struct3) deq_rsToProc_aa ();
    method ActionValue#(Struct3) deq_rsToProc_a ();
endinterface

module mkModule1 (Module1);
    Reg#(Vector#(8, Struct2)) elt_rqFromProc_aa <- mkReg(vec(Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}));
    Reg#(Vector#(8, Struct2)) elt_rqFromProc_a <- mkReg(vec(Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}, Struct2 {addr: 4'h0, op: False, data: 32'h0}));
    Reg#(Bit#(3)) enqP_rqFromProc_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) enqP_rqFromProc_a <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rqFromProc_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rqFromProc_a <- mkReg(3'h0);
    Reg#(Bool) empty_rqFromProc_aa <- mkReg(True);
    Reg#(Bool) empty_rqFromProc_a <- mkReg(True);
    Reg#(Bool) full_rqFromProc_aa <- mkReg(False);
    Reg#(Bool) full_rqFromProc_a <- mkReg(False);
    Reg#(Vector#(8, Struct3)) elt_rsToProc_aa <- mkReg(vec(Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}));
    Reg#(Vector#(8, Struct3)) elt_rsToProc_a <- mkReg(vec(Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}, Struct3 {data: 32'h0}));
    Reg#(Bit#(3)) enqP_rsToProc_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) enqP_rsToProc_a <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rsToProc_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rsToProc_a <- mkReg(3'h0);
    Reg#(Bool) empty_rsToProc_aa <- mkReg(True);
    Reg#(Bool) empty_rsToProc_a <- mkReg(True);
    Reg#(Bool) full_rsToProc_aa <- mkReg(False);
    Reg#(Bool) full_rsToProc_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_rqFromProc_aa (Struct2 x_0);
        let x_1 = (full_rqFromProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_aa);
        let x_3 = (enqP_rqFromProc_aa);
        let x_4 = (deqP_rqFromProc_aa);
        elt_rqFromProc_aa <= update (x_2, x_3, x_0);
        empty_rqFromProc_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rqFromProc_aa <= x_4 == x_5;
        enqP_rqFromProc_aa <= x_5;
        
    endmethod
    
    method Action enq_rqFromProc_a (Struct2 x_0);
        let x_1 = (full_rqFromProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_a);
        let x_3 = (enqP_rqFromProc_a);
        let x_4 = (deqP_rqFromProc_a);
        elt_rqFromProc_a <= update (x_2, x_3, x_0);
        empty_rqFromProc_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rqFromProc_a <= x_4 == x_5;
        enqP_rqFromProc_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct2) deq_rqFromProc_aa ();
        let x_1 = (empty_rqFromProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_aa);
        let x_3 = (enqP_rqFromProc_aa);
        let x_4 = (deqP_rqFromProc_aa);
        full_rqFromProc_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rqFromProc_aa <= x_3 == x_5;
        deqP_rqFromProc_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct2) deq_rqFromProc_a ();
        let x_1 = (empty_rqFromProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_a);
        let x_3 = (enqP_rqFromProc_a);
        let x_4 = (deqP_rqFromProc_a);
        full_rqFromProc_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rqFromProc_a <= x_3 == x_5;
        deqP_rqFromProc_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct2) firstElt_rqFromProc_aa ();
        let x_1 = (empty_rqFromProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_aa);
        let x_3 = (deqP_rqFromProc_aa);
        return (x_2)[x_3];
    endmethod
    
    method ActionValue#(Struct2) firstElt_rqFromProc_a ();
        let x_1 = (empty_rqFromProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_a);
        let x_3 = (deqP_rqFromProc_a);
        return (x_2)[x_3];
    endmethod
    
    method Action enq_rsToProc_aa (Struct3 x_0);
        let x_1 = (full_rsToProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_aa);
        let x_3 = (enqP_rsToProc_aa);
        let x_4 = (deqP_rsToProc_aa);
        elt_rsToProc_aa <= update (x_2, x_3, x_0);
        empty_rsToProc_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rsToProc_aa <= x_4 == x_5;
        enqP_rsToProc_aa <= x_5;
        
    endmethod
    
    method Action enq_rsToProc_a (Struct3 x_0);
        let x_1 = (full_rsToProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_a);
        let x_3 = (enqP_rsToProc_a);
        let x_4 = (deqP_rsToProc_a);
        elt_rsToProc_a <= update (x_2, x_3, x_0);
        empty_rsToProc_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rsToProc_a <= x_4 == x_5;
        enqP_rsToProc_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct3) deq_rsToProc_aa ();
        let x_1 = (empty_rsToProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_aa);
        let x_3 = (enqP_rsToProc_aa);
        let x_4 = (deqP_rsToProc_aa);
        full_rsToProc_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rsToProc_aa <= x_3 == x_5;
        deqP_rsToProc_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct3) deq_rsToProc_a ();
        let x_1 = (empty_rsToProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_a);
        let x_3 = (enqP_rsToProc_a);
        let x_4 = (deqP_rsToProc_a);
        full_rsToProc_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rsToProc_a <= x_3 == x_5;
        deqP_rsToProc_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module2;
    method ActionValue#(Bit#(2)) read_cs_aa (Bit#(2) x_0);
    method ActionValue#(Bit#(2)) read_cs_a (Bit#(2) x_0);
    method Action write_cs_aa (Struct5 x_0);
    method Action write_cs_a (Struct5 x_0);
endinterface

module mkModule2 (Module2);
    Reg#(Vector#(4, Bit#(2))) dataArray_cs_aa <- mkReg(vec(2'h0, 2'h0, 2'h0, 2'h0));
    Reg#(Vector#(4, Bit#(2))) dataArray_cs_a <- mkReg(vec(2'h0, 2'h0, 2'h0, 2'h0));
    
    // No rules in this module
    
    method ActionValue#(Bit#(2)) read_cs_aa (Bit#(2) x_0);
        let x_1 = (dataArray_cs_aa);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(2)) read_cs_a (Bit#(2) x_0);
        let x_1 = (dataArray_cs_a);
        return (x_1)[x_0];
    endmethod
    
    method Action write_cs_aa (Struct5 x_0);
        let x_1 = (dataArray_cs_aa);
        dataArray_cs_aa <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
    method Action write_cs_a (Struct5 x_0);
        let x_1 = (dataArray_cs_a);
        dataArray_cs_a <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
endmodule

interface Module3;
    method ActionValue#(Bit#(1)) read_tag_aa (Bit#(2) x_0);
    method ActionValue#(Bit#(1)) read_tag_a (Bit#(2) x_0);
    method Action write_tag_aa (Struct8 x_0);
    method Action write_tag_a (Struct8 x_0);
endinterface

module mkModule3 (Module3);
    Reg#(Vector#(4, Bit#(1))) dataArray_tag_aa <- mkReg(vec(1'h0, 1'h0, 1'h0, 1'h0));
    Reg#(Vector#(4, Bit#(1))) dataArray_tag_a <- mkReg(vec(1'h0, 1'h0, 1'h0, 1'h0));
    
    // No rules in this module
    
    method ActionValue#(Bit#(1)) read_tag_aa (Bit#(2) x_0);
        let x_1 = (dataArray_tag_aa);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(1)) read_tag_a (Bit#(2) x_0);
        let x_1 = (dataArray_tag_a);
        return (x_1)[x_0];
    endmethod
    
    method Action write_tag_aa (Struct8 x_0);
        let x_1 = (dataArray_tag_aa);
        dataArray_tag_aa <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
    method Action write_tag_a (Struct8 x_0);
        let x_1 = (dataArray_tag_a);
        dataArray_tag_a <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
endmodule

interface Module4;
    method ActionValue#(Vector#(2, Bit#(32))) read_line_aa (Bit#(2) x_0);
    method ActionValue#(Vector#(2, Bit#(32))) read_line_a (Bit#(2) x_0);
    method Action write_line_aa (Struct9 x_0);
    method Action write_line_a (Struct9 x_0);
endinterface

module mkModule4 (Module4);
    Reg#(Vector#(4, Vector#(2, Bit#(32)))) dataArray_line_aa <- mkReg(vec(vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0)));
    Reg#(Vector#(4, Vector#(2, Bit#(32)))) dataArray_line_a <- mkReg(vec(vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0)));
    
    // No rules in this module
    
    method ActionValue#(Vector#(2, Bit#(32))) read_line_aa (Bit#(2) x_0);
        let x_1 = (dataArray_line_aa);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Vector#(2, Bit#(32))) read_line_a (Bit#(2) x_0);
        let x_1 = (dataArray_line_a);
        return (x_1)[x_0];
    endmethod
    
    method Action write_line_aa (Struct9 x_0);
        let x_1 = (dataArray_line_aa);
        dataArray_line_aa <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
    method Action write_line_a (Struct9 x_0);
        let x_1 = (dataArray_line_a);
        dataArray_line_a <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
endmodule

interface Module5;
    method Action enq_rqToParent_aa (Struct6 x_0);
    method Action enq_rqToParent_a (Struct6 x_0);
    method ActionValue#(Struct6) deq_rqToParent_aa ();
    method ActionValue#(Struct6) deq_rqToParent_a ();
endinterface

module mkModule5 (Module5);
    Reg#(Vector#(8, Struct6)) elt_rqToParent_aa <- mkReg(vec(Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}));
    Reg#(Vector#(8, Struct6)) elt_rqToParent_a <- mkReg(vec(Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}, Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}));
    Reg#(Bit#(3)) enqP_rqToParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) enqP_rqToParent_a <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rqToParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rqToParent_a <- mkReg(3'h0);
    Reg#(Bool) empty_rqToParent_aa <- mkReg(True);
    Reg#(Bool) empty_rqToParent_a <- mkReg(True);
    Reg#(Bool) full_rqToParent_aa <- mkReg(False);
    Reg#(Bool) full_rqToParent_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_rqToParent_aa (Struct6 x_0);
        let x_1 = (full_rqToParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqToParent_aa);
        let x_3 = (enqP_rqToParent_aa);
        let x_4 = (deqP_rqToParent_aa);
        elt_rqToParent_aa <= update (x_2, x_3, x_0);
        empty_rqToParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rqToParent_aa <= x_4 == x_5;
        enqP_rqToParent_aa <= x_5;
        
    endmethod
    
    method Action enq_rqToParent_a (Struct6 x_0);
        let x_1 = (full_rqToParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqToParent_a);
        let x_3 = (enqP_rqToParent_a);
        let x_4 = (deqP_rqToParent_a);
        elt_rqToParent_a <= update (x_2, x_3, x_0);
        empty_rqToParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rqToParent_a <= x_4 == x_5;
        enqP_rqToParent_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct6) deq_rqToParent_aa ();
        let x_1 = (empty_rqToParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqToParent_aa);
        let x_3 = (enqP_rqToParent_aa);
        let x_4 = (deqP_rqToParent_aa);
        full_rqToParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rqToParent_aa <= x_3 == x_5;
        deqP_rqToParent_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct6) deq_rqToParent_a ();
        let x_1 = (empty_rqToParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqToParent_a);
        let x_3 = (enqP_rqToParent_a);
        let x_4 = (deqP_rqToParent_a);
        full_rqToParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rqToParent_a <= x_3 == x_5;
        deqP_rqToParent_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module6;
    method Action enq_rsToParent_aa (Struct4 x_0);
    method Action enq_rsToParent_a (Struct4 x_0);
    method ActionValue#(Struct4) deq_rsToParent_aa ();
    method ActionValue#(Struct4) deq_rsToParent_a ();
endinterface

module mkModule6 (Module6);
    Reg#(Vector#(8, Struct4)) elt_rsToParent_aa <- mkReg(vec(Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}));
    Reg#(Vector#(8, Struct4)) elt_rsToParent_a <- mkReg(vec(Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}, Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}));
    Reg#(Bit#(3)) enqP_rsToParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) enqP_rsToParent_a <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rsToParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rsToParent_a <- mkReg(3'h0);
    Reg#(Bool) empty_rsToParent_aa <- mkReg(True);
    Reg#(Bool) empty_rsToParent_a <- mkReg(True);
    Reg#(Bool) full_rsToParent_aa <- mkReg(False);
    Reg#(Bool) full_rsToParent_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_rsToParent_aa (Struct4 x_0);
        let x_1 = (full_rsToParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToParent_aa);
        let x_3 = (enqP_rsToParent_aa);
        let x_4 = (deqP_rsToParent_aa);
        elt_rsToParent_aa <= update (x_2, x_3, x_0);
        empty_rsToParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rsToParent_aa <= x_4 == x_5;
        enqP_rsToParent_aa <= x_5;
        
    endmethod
    
    method Action enq_rsToParent_a (Struct4 x_0);
        let x_1 = (full_rsToParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToParent_a);
        let x_3 = (enqP_rsToParent_a);
        let x_4 = (deqP_rsToParent_a);
        elt_rsToParent_a <= update (x_2, x_3, x_0);
        empty_rsToParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rsToParent_a <= x_4 == x_5;
        enqP_rsToParent_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct4) deq_rsToParent_aa ();
        let x_1 = (empty_rsToParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToParent_aa);
        let x_3 = (enqP_rsToParent_aa);
        let x_4 = (deqP_rsToParent_aa);
        full_rsToParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rsToParent_aa <= x_3 == x_5;
        deqP_rsToParent_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct4) deq_rsToParent_a ();
        let x_1 = (empty_rsToParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToParent_a);
        let x_3 = (enqP_rsToParent_a);
        let x_4 = (deqP_rsToParent_a);
        full_rsToParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rsToParent_a <= x_3 == x_5;
        deqP_rsToParent_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module7;
    method Action enq_fromParent_aa (Struct7 x_0);
    method Action enq_fromParent_a (Struct7 x_0);
    method ActionValue#(Struct7) deq_fromParent_aa ();
    method ActionValue#(Struct7) deq_fromParent_a ();
endinterface

module mkModule7 (Module7);
    Reg#(Vector#(8, Struct7)) elt_fromParent_aa <- mkReg(vec(Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}));
    Reg#(Vector#(8, Struct7)) elt_fromParent_a <- mkReg(vec(Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}, Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}));
    Reg#(Bit#(3)) enqP_fromParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) enqP_fromParent_a <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_fromParent_aa <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_fromParent_a <- mkReg(3'h0);
    Reg#(Bool) empty_fromParent_aa <- mkReg(True);
    Reg#(Bool) empty_fromParent_a <- mkReg(True);
    Reg#(Bool) full_fromParent_aa <- mkReg(False);
    Reg#(Bool) full_fromParent_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_fromParent_aa (Struct7 x_0);
        let x_1 = (full_fromParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_fromParent_aa);
        let x_3 = (enqP_fromParent_aa);
        let x_4 = (deqP_fromParent_aa);
        elt_fromParent_aa <= update (x_2, x_3, x_0);
        empty_fromParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_fromParent_aa <= x_4 == x_5;
        enqP_fromParent_aa <= x_5;
        
    endmethod
    
    method Action enq_fromParent_a (Struct7 x_0);
        let x_1 = (full_fromParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_fromParent_a);
        let x_3 = (enqP_fromParent_a);
        let x_4 = (deqP_fromParent_a);
        elt_fromParent_a <= update (x_2, x_3, x_0);
        empty_fromParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_fromParent_a <= x_4 == x_5;
        enqP_fromParent_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct7) deq_fromParent_aa ();
        let x_1 = (empty_fromParent_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_fromParent_aa);
        let x_3 = (enqP_fromParent_aa);
        let x_4 = (deqP_fromParent_aa);
        full_fromParent_aa <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_fromParent_aa <= x_3 == x_5;
        deqP_fromParent_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct7) deq_fromParent_a ();
        let x_1 = (empty_fromParent_a);
        when (! (x_1), noAction);
        let x_2 = (elt_fromParent_a);
        let x_3 = (enqP_fromParent_a);
        let x_4 = (deqP_fromParent_a);
        full_fromParent_a <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_fromParent_a <= x_3 == x_5;
        deqP_fromParent_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module8;
    method Action enq_rqFromChild (Struct10 x_0);
    method ActionValue#(Struct10) deq_rqFromChild ();
    method ActionValue#(Struct10) firstElt_rqFromChild ();
endinterface

module mkModule8 (Module8);
    Reg#(Vector#(8, Struct10)) elt_rqFromChild <- mkReg(vec(Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}, Struct10 {child: 1'h0, rq: Struct6 {addr: 3'h0, from: 2'h0, to: 2'h0, id: 1'h0}}));
    Reg#(Bit#(3)) enqP_rqFromChild <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rqFromChild <- mkReg(3'h0);
    Reg#(Bool) empty_rqFromChild <- mkReg(True);
    Reg#(Bool) full_rqFromChild <- mkReg(False);
    // No rules in this module
    
    method Action enq_rqFromChild (Struct10 x_0);
        let x_1 = (full_rqFromChild);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromChild);
        let x_3 = (enqP_rqFromChild);
        let x_4 = (deqP_rqFromChild);
        elt_rqFromChild <= update (x_2, x_3, x_0);
        empty_rqFromChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rqFromChild <= x_4 == x_5;
        enqP_rqFromChild <= x_5;
        
    endmethod
    
    method ActionValue#(Struct10) deq_rqFromChild ();
        let x_1 = (empty_rqFromChild);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromChild);
        let x_3 = (enqP_rqFromChild);
        let x_4 = (deqP_rqFromChild);
        full_rqFromChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rqFromChild <= x_3 == x_5;
        deqP_rqFromChild <= x_5;
        return (x_2)[x_4];
    endmethod
    
    method ActionValue#(Struct10) firstElt_rqFromChild ();
        let x_1 = (empty_rqFromChild);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromChild);
        let x_3 = (deqP_rqFromChild);
        return (x_2)[x_3];
    endmethod
    
endmodule

interface Module9;
    method Action enq_rsFromChild (Struct11 x_0);
    method ActionValue#(Struct11) deq_rsFromChild ();
endinterface

module mkModule9 (Module9);
    Reg#(Vector#(8, Struct11)) elt_rsFromChild <- mkReg(vec(Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}, Struct11 {child: 1'h0, rs: Struct4 {addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), isVol: False}}));
    Reg#(Bit#(3)) enqP_rsFromChild <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_rsFromChild <- mkReg(3'h0);
    Reg#(Bool) empty_rsFromChild <- mkReg(True);
    Reg#(Bool) full_rsFromChild <- mkReg(False);
    // No rules in this module
    
    method Action enq_rsFromChild (Struct11 x_0);
        let x_1 = (full_rsFromChild);
        when (! (x_1), noAction);
        let x_2 = (elt_rsFromChild);
        let x_3 = (enqP_rsFromChild);
        let x_4 = (deqP_rsFromChild);
        elt_rsFromChild <= update (x_2, x_3, x_0);
        empty_rsFromChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_rsFromChild <= x_4 == x_5;
        enqP_rsFromChild <= x_5;
        
    endmethod
    
    method ActionValue#(Struct11) deq_rsFromChild ();
        let x_1 = (empty_rsFromChild);
        when (! (x_1), noAction);
        let x_2 = (elt_rsFromChild);
        let x_3 = (enqP_rsFromChild);
        let x_4 = (deqP_rsFromChild);
        full_rsFromChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_rsFromChild <= x_3 == x_5;
        deqP_rsFromChild <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module10;
    method Action enq_toChild (Struct12 x_0);
    method ActionValue#(Struct12) deq_toChild ();
endinterface

module mkModule10 (Module10);
    Reg#(Vector#(8, Struct12)) elt_toChild <- mkReg(vec(Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}, Struct12 {child: 1'h0, msg: Struct7 {isRq: False, addr: 3'h0, to: 2'h0, line: vec(32'h0, 32'h0), id: 1'h0}}));
    Reg#(Bit#(3)) enqP_toChild <- mkReg(3'h0);
    Reg#(Bit#(3)) deqP_toChild <- mkReg(3'h0);
    Reg#(Bool) empty_toChild <- mkReg(True);
    Reg#(Bool) full_toChild <- mkReg(False);
    // No rules in this module
    
    method Action enq_toChild (Struct12 x_0);
        let x_1 = (full_toChild);
        when (! (x_1), noAction);
        let x_2 = (elt_toChild);
        let x_3 = (enqP_toChild);
        let x_4 = (deqP_toChild);
        elt_toChild <= update (x_2, x_3, x_0);
        empty_toChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_3) + ((Bit#(3))'(3'h1)));
        full_toChild <= x_4 == x_5;
        enqP_toChild <= x_5;
        
    endmethod
    
    method ActionValue#(Struct12) deq_toChild ();
        let x_1 = (empty_toChild);
        when (! (x_1), noAction);
        let x_2 = (elt_toChild);
        let x_3 = (enqP_toChild);
        let x_4 = (deqP_toChild);
        full_toChild <= (Bool)'(False);
        Bit#(3) x_5 = ((x_4) + ((Bit#(3))'(3'h1)));
        empty_toChild <= x_3 == x_5;
        deqP_toChild <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module11;
    method ActionValue#(Vector#(2, Bit#(32))) read_mline (Bit#(3) x_0);
    method Action write_mline (Struct15 x_0);
endinterface

module mkModule11 (Module11);
    Reg#(Vector#(8, Vector#(2, Bit#(32)))) dataArray_mline <- mkReg(vec(vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0), vec(32'h0, 32'h0)));
    
    // No rules in this module
    
    method ActionValue#(Vector#(2, Bit#(32))) read_mline (Bit#(3) x_0);
        let x_1 = (dataArray_mline);
        return (x_1)[x_0];
    endmethod
    
    method Action write_mline (Struct15 x_0);
        let x_1 = (dataArray_mline);
        dataArray_mline <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
endmodule

interface Module12;
    method ActionValue#(Vector#(2, Bit#(2))) read_mcs (Bit#(3) x_0);
    method Action write_mcs (Struct14 x_0);
endinterface

module mkModule12 (Module12);
    Reg#(Vector#(8, Vector#(2, Bit#(2)))) dataArray_mcs <- mkReg(vec(vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0), vec(2'h0, 2'h0)));
    
    // No rules in this module
    
    method ActionValue#(Vector#(2, Bit#(2))) read_mcs (Bit#(3) x_0);
        let x_1 = (dataArray_mcs);
        return (x_1)[x_0];
    endmethod
    
    method Action write_mcs (Struct14 x_0);
        let x_1 = (dataArray_mcs);
        dataArray_mcs <= update (x_1, (x_0).addr, (x_0).data);
        
    endmethod
    
endmodule

interface Module13; 
endinterface


module mkModule13#(function Action toHost_aa(Bit#(32) _),
  function ActionValue#(Struct3) deq_rsToProc_aa(),
  function Action enq_rqFromProc_aa(Struct2 _)) (Module13);
    Reg#(Bit#(4)) pc_aa <- mkReg(4'h0);
    Reg#(Vector#(32, Bit#(32))) rf_aa <- mkReg(vec(32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0));
    Reg#(Bool) stall_aa <- mkReg(False);
    
    rule reqLd_aa;
        let x_0 = (stall_aa);
        when (! (x_0), noAction);
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h3), noAction);
        let x_4 <- enq_rqFromProc_aa(Struct2 {addr : (x_3).addr, op :
        (Bool)'(False), data : (Bit#(32))'(32'h0)});
        stall_aa <= (Bool)'(True);
        
    endrule
    
    rule reqSt_aa;
        let x_0 = (stall_aa);
        when (! (x_0), noAction);
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h23), noAction);
        let x_4 <- enq_rqFromProc_aa(Struct2 {addr : (x_3).addr, op :
        (Bool)'(True), data : (x_3).value});
        stall_aa <= (Bool)'(True);
        
    endrule
    
    rule repLd_aa;
        let x_0 <- deq_rsToProc_aa();
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h3), noAction);
        rf_aa <= update (x_2, (x_3).reg_, (x_0).data);
        stall_aa <= (Bool)'(False);
        pc_aa <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    rule repSt_aa;
        let x_0 <- deq_rsToProc_aa();
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h23), noAction);
        stall_aa <= (Bool)'(False);
        pc_aa <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    rule execToHost_aa;
        let x_0 = (stall_aa);
        when (! (x_0), noAction);
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h8), noAction);
        let x_4 <- toHost_aa((x_3).value);
        
    endrule
    
    rule execNm_aa;
        let x_0 = (stall_aa);
        when (! (x_0), noAction);
        let x_1 = (pc_aa);
        let x_2 = (rf_aa);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when (! ((((x_3).opcode == (Bit#(7))'(7'h3)) || ((x_3).opcode ==
        (Bit#(7))'(7'h23))) || ((x_3).opcode == (Bit#(7))'(7'h8))),
        noAction);
        rf_aa <= (x_3).opcode == (Bit#(7))'(7'h6f) ? (update (x_2,
        ((x_3).inst)[11:7], (zeroExtend(x_1)) +
        (zeroExtend({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})}))))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (update (x_2,
        ((x_3).inst)[11:7], zeroExtend(((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))))) : ((x_3).opcode ==
        (Bit#(7))'(7'h33) ? (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ?
        (update (x_2, ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) +
        ((x_2)[((x_3).inst)[24:20]]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h20) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) - ((x_2)[((x_3).inst)[24:20]]))) :
        (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) <<
        (((x_2)[((x_3).inst)[24:20]])[4:0]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) >> (((x_2)[((x_3).inst)[24:20]])[4:0])))
        : (((x_3).inst)[31:25] == (Bit#(7))'(7'h20) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) >>
        (((x_2)[((x_3).inst)[24:20]])[4:0]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) | ((x_2)[((x_3).inst)[24:20]]))) :
        (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) &
        ((x_2)[((x_3).inst)[24:20]]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) ^ ((x_2)[((x_3).inst)[24:20]]))) :
        (x_2))))))))) : ((x_3).opcode == (Bit#(7))'(7'h13) ?
        (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) +
        (zeroExtend(((x_3).inst)[31:20])))) : (x_2)) : (x_2))));
        pc_aa <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    // No methods in this module
endmodule

interface Module14; 
endinterface


module mkModule14#(function Action toHost_a(Bit#(32) _),
  function ActionValue#(Struct3) deq_rsToProc_a(),
  function Action enq_rqFromProc_a(Struct2 _)) (Module14);
    Reg#(Bit#(4)) pc_a <- mkReg(4'h0);
    Reg#(Vector#(32, Bit#(32))) rf_a <- mkReg(vec(32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0));
    Reg#(Bool) stall_a <- mkReg(False);
    
    rule reqLd_a;
        let x_0 = (stall_a);
        when (! (x_0), noAction);
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h3), noAction);
        let x_4 <- enq_rqFromProc_a(Struct2 {addr : (x_3).addr, op :
        (Bool)'(False), data : (Bit#(32))'(32'h0)});
        stall_a <= (Bool)'(True);
        
    endrule
    
    rule reqSt_a;
        let x_0 = (stall_a);
        when (! (x_0), noAction);
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h23), noAction);
        let x_4 <- enq_rqFromProc_a(Struct2 {addr : (x_3).addr, op :
        (Bool)'(True), data : (x_3).value});
        stall_a <= (Bool)'(True);
        
    endrule
    
    rule repLd_a;
        let x_0 <- deq_rsToProc_a();
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h3), noAction);
        rf_a <= update (x_2, (x_3).reg_, (x_0).data);
        stall_a <= (Bool)'(False);
        pc_a <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    rule repSt_a;
        let x_0 <- deq_rsToProc_a();
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h23), noAction);
        stall_a <= (Bool)'(False);
        pc_a <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    rule execToHost_a;
        let x_0 = (stall_a);
        when (! (x_0), noAction);
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when ((x_3).opcode == (Bit#(7))'(7'h8), noAction);
        let x_4 <- toHost_a((x_3).value);
        
    endrule
    
    rule execNm_a;
        let x_0 = (stall_a);
        when (! (x_0), noAction);
        let x_1 = (pc_a);
        let x_2 = (rf_a);
        Struct1 x_3 =
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h3) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7],
        addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:20])),
        value : (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h23) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]]))
        +
        (truncate({((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[31:25]),((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[11:7])})),
        value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[24:20]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        :
        ((((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0]
        == (Bit#(7))'(7'h8) ? (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (x_2)[(((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[19:15]],
        inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]})
        : (Struct1 {opcode :
        (((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1])[6:0],
        reg_ : (Bit#(5))'(5'h0), addr : (Bit#(4))'(4'h0), value :
        (Bit#(32))'(32'h0), inst :
        ((Vector#(16, Bit#(32)))'(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h100293, 32'h1c0006f, 32'h13, 32'h13)))[x_1]}))));
        
        when (! ((((x_3).opcode == (Bit#(7))'(7'h3)) || ((x_3).opcode ==
        (Bit#(7))'(7'h23))) || ((x_3).opcode == (Bit#(7))'(7'h8))),
        noAction);
        rf_a <= (x_3).opcode == (Bit#(7))'(7'h6f) ? (update (x_2,
        ((x_3).inst)[11:7], (zeroExtend(x_1)) +
        (zeroExtend({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})}))))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (update (x_2,
        ((x_3).inst)[11:7], zeroExtend(((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))))) : ((x_3).opcode ==
        (Bit#(7))'(7'h33) ? (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ?
        (update (x_2, ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) +
        ((x_2)[((x_3).inst)[24:20]]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h20) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) - ((x_2)[((x_3).inst)[24:20]]))) :
        (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) <<
        (((x_2)[((x_3).inst)[24:20]])[4:0]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) >> (((x_2)[((x_3).inst)[24:20]])[4:0])))
        : (((x_3).inst)[31:25] == (Bit#(7))'(7'h20) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) >>
        (((x_2)[((x_3).inst)[24:20]])[4:0]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) | ((x_2)[((x_3).inst)[24:20]]))) :
        (((x_3).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) &
        ((x_2)[((x_3).inst)[24:20]]))) : (((x_3).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_2, ((x_3).inst)[11:7],
        ((x_2)[((x_3).inst)[19:15]]) ^ ((x_2)[((x_3).inst)[24:20]]))) :
        (x_2))))))))) : ((x_3).opcode == (Bit#(7))'(7'h13) ?
        (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ? (update (x_2,
        ((x_3).inst)[11:7], ((x_2)[((x_3).inst)[19:15]]) +
        (zeroExtend(((x_3).inst)[31:20])))) : (x_2)) : (x_2))));
        pc_a <= (x_3).opcode == (Bit#(7))'(7'h6f) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[19:12])}),({(((x_3).inst)[20:20]),(((x_3).inst)[30:21])})})))
        : ((x_3).opcode == (Bit#(7))'(7'h67) ? (((x_1) +
        (truncate((x_2)[((x_3).inst)[19:15]]))) +
        (truncate(((x_3).inst)[31:20]))) : ((x_3).opcode == (Bit#(7))'(7'h63)
        ? (((x_3).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_2)[((x_3).inst)[19:15]] == (x_2)[((x_3).inst)[24:20]] ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_2)[((x_3).inst)[19:15]] ==
        (x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]]) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : (((x_3).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_2)[((x_3).inst)[19:15]]) <
        ((x_2)[((x_3).inst)[24:20]])) ? ((x_1) +
        (truncate({({(((x_3).inst)[31:31]),(((x_3).inst)[7:7])}),({(((x_3).inst)[30:25]),(((x_3).inst)[11:8])})})))
        : ((x_1) + ((Bit#(4))'(4'h1)))) : ((x_1) + ((Bit#(4))'(4'h1))))))) :
        ((x_1) + ((Bit#(4))'(4'h1)))));
        
    endrule
    
    // No methods in this module
endmodule

interface Module15; 
endinterface


module mkModule15#(function ActionValue#(Struct2) deq_rqFromProc_a(),
  function Action enq_rsToProc_a(Struct3 _),
  function ActionValue#(Struct2) deq_rqFromProc_aa(),
  function Action enq_rsToProc_aa(Struct3 _),
  function Action write_line_a(Struct9 _),
  function Action write_tag_a(Struct8 _),
  function ActionValue#(Struct7) deq_fromParent_a(),
  function Action write_line_aa(Struct9 _),
  function Action write_tag_aa(Struct8 _),
  function ActionValue#(Struct7) deq_fromParent_aa(),
  function Action enq_rqToParent_a(Struct6 _),
  function Action enq_rqToParent_aa(Struct6 _),
  function Action write_cs_a(Struct5 _),
  function Action enq_rsToParent_a(Struct4 _),
  function ActionValue#(Vector#(2, Bit#(32))) read_line_a(Bit#(2) _),
  function Action write_cs_aa(Struct5 _),
  function Action enq_rsToParent_aa(Struct4 _),
  function ActionValue#(Vector#(2, Bit#(32))) read_line_aa(Bit#(2) _),
  function ActionValue#(Bit#(2)) read_cs_a(Bit#(2) _),
  function ActionValue#(Bit#(1)) read_tag_a(Bit#(2) _),
  function ActionValue#(Struct2) firstElt_rqFromProc_a(),
  function ActionValue#(Bit#(2)) read_cs_aa(Bit#(2) _),
  function ActionValue#(Bit#(1)) read_tag_aa(Bit#(2) _),
  function ActionValue#(Struct2) firstElt_rqFromProc_aa()) (Module15);
    Reg#(Bool) procRqValid_aa <- mkReg(False);
    Reg#(Bool) procRqValid_a <- mkReg(False);
    Reg#(Bool) procRqReplace_aa <- mkReg(False);
    Reg#(Bool) procRqReplace_a <- mkReg(False);
    Reg#(Bool) procRqWait_aa <- mkReg(False);
    Reg#(Bool) procRqWait_a <- mkReg(False);
    Reg#(Struct2) procRq_aa <- mkReg(Struct2 {addr: 4'h0, op: False, data: 32'h0});
    Reg#(Struct2) procRq_a <- mkReg(Struct2 {addr: 4'h0, op: False, data: 32'h0});
    
    
    rule l1MissByState_aa;
        let x_0 = (procRqValid_aa);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_aa();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_aa(x_2);
        let x_4 <- read_cs_aa(x_2);
        when (((x_3 == (((x_1).addr)[3:1])[2:2]) && (x_4 ==
        (Bit#(2))'(2'h1))) && ((x_1).op), noAction);
        procRqValid_aa <= (Bool)'(True);
        procRqReplace_aa <= (Bool)'(False);
        procRqWait_aa <= (Bool)'(False);
        procRq_aa <= x_1;
        
    endrule
    
    rule l1MissByState_a;
        let x_0 = (procRqValid_a);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_a();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_a(x_2);
        let x_4 <- read_cs_a(x_2);
        when (((x_3 == (((x_1).addr)[3:1])[2:2]) && (x_4 ==
        (Bit#(2))'(2'h1))) && ((x_1).op), noAction);
        procRqValid_a <= (Bool)'(True);
        procRqReplace_a <= (Bool)'(False);
        procRqWait_a <= (Bool)'(False);
        procRq_a <= x_1;
        
    endrule
    
    rule l1MissByLine_aa;
        let x_0 = (procRqValid_aa);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_aa();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_aa(x_2);
        let x_4 <- read_cs_aa(x_2);
        when ((! (x_3 == (((x_1).addr)[3:1])[2:2])) || (x_4 ==
        (Bit#(2))'(2'h0)), noAction);
        procRqValid_aa <= (Bool)'(True);
        procRqReplace_aa <= (Bool)'(True);
        procRqWait_aa <= (Bool)'(False);
        procRq_aa <= x_1;
        
    endrule
    
    rule l1MissByLine_a;
        let x_0 = (procRqValid_a);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_a();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_a(x_2);
        let x_4 <- read_cs_a(x_2);
        when ((! (x_3 == (((x_1).addr)[3:1])[2:2])) || (x_4 ==
        (Bit#(2))'(2'h0)), noAction);
        procRqValid_a <= (Bool)'(True);
        procRqReplace_a <= (Bool)'(True);
        procRqWait_a <= (Bool)'(False);
        procRq_a <= x_1;
        
    endrule
    
    rule l1Hit_aa;
        let x_0 = (procRqValid_aa);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_aa();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_aa(x_2);
        let x_4 <- read_cs_aa(x_2);
        when ((x_3 == (((x_1).addr)[3:1])[2:2]) && (((x_4 ==
        (Bit#(2))'(2'h1)) && (! ((x_1).op))) || ((x_4 == (Bit#(2))'(2'h3)) &&
        ((x_1).op))), noAction);
        procRqValid_aa <= (Bool)'(True);
        procRqReplace_aa <= (Bool)'(False);
        procRqWait_aa <= (Bool)'(False);
        procRq_aa <= x_1;
        
    endrule
    
    rule l1Hit_a;
        let x_0 = (procRqValid_a);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromProc_a();
        Bit#(2) x_2 = ((((x_1).addr)[3:1])[1:0]);
        let x_3 <- read_tag_a(x_2);
        let x_4 <- read_cs_a(x_2);
        when ((x_3 == (((x_1).addr)[3:1])[2:2]) && (((x_4 ==
        (Bit#(2))'(2'h1)) && (! ((x_1).op))) || ((x_4 == (Bit#(2))'(2'h3)) &&
        ((x_1).op))), noAction);
        procRqValid_a <= (Bool)'(True);
        procRqReplace_a <= (Bool)'(False);
        procRqWait_a <= (Bool)'(False);
        procRq_a <= x_1;
        
    endrule
    
    rule writeback_aa;
        let x_0 = (procRqValid_aa);
        when (x_0, noAction);
        let x_1 = (procRqReplace_aa);
        when (x_1, noAction);
        let x_2 = (procRq_aa);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_aa(x_3);
        let x_5 <- read_cs_aa(x_3);
        let x_6 <- read_line_aa(x_3);
        if (! (x_5 == (Bit#(2))'(2'h0))) begin
            let x_7 <- enq_rsToParent_aa(Struct4 {addr : {(x_4),(x_3)}, to :
            (Bit#(2))'(2'h0), line : x_6, isVol : (Bool)'(True)});
            
        end else begin
        end
        let x_9 <- write_cs_aa(Struct5 {addr : x_3, data :
        (Bit#(2))'(2'h0)});
        procRqReplace_aa <= (Bool)'(False);
        
    endrule
    
    rule writeback_a;
        let x_0 = (procRqValid_a);
        when (x_0, noAction);
        let x_1 = (procRqReplace_a);
        when (x_1, noAction);
        let x_2 = (procRq_a);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_a(x_3);
        let x_5 <- read_cs_a(x_3);
        let x_6 <- read_line_a(x_3);
        if (! (x_5 == (Bit#(2))'(2'h0))) begin
            let x_7 <- enq_rsToParent_a(Struct4 {addr : {(x_4),(x_3)}, to :
            (Bit#(2))'(2'h0), line : x_6, isVol : (Bool)'(True)});
            
        end else begin
        end
        let x_9 <- write_cs_a(Struct5 {addr : x_3, data : (Bit#(2))'(2'h0)});
        
        procRqReplace_a <= (Bool)'(False);
        
    endrule
    
    rule upgRq_aa;
        let x_0 = (procRqValid_aa);
        when (x_0, noAction);
        let x_1 = (procRqReplace_aa);
        when (! (x_1), noAction);
        let x_2 = (procRq_aa);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_cs_aa(x_3);
        Bit#(2) x_5 = ((x_2).op ? ((Bit#(2))'(2'h3)) : ((Bit#(2))'(2'h1)));
        
        let x_6 = (procRqWait_aa);
        let x_7 <- read_tag_aa(x_3);
        when ((! (x_6)) && ((x_4 == (Bit#(2))'(2'h0)) || ((x_7 ==
        (((x_2).addr)[3:1])[2:2]) && ((x_4) < (x_5)))), noAction);
        let x_8 <- enq_rqToParent_aa(Struct6 {addr : ((x_2).addr)[3:1], from
        : x_4, to : x_5, id : (Bit#(1))'(1'h0)});
        procRqWait_aa <= (Bool)'(True);
        
    endrule
    
    rule upgRq_a;
        let x_0 = (procRqValid_a);
        when (x_0, noAction);
        let x_1 = (procRqReplace_a);
        when (! (x_1), noAction);
        let x_2 = (procRq_a);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_cs_a(x_3);
        Bit#(2) x_5 = ((x_2).op ? ((Bit#(2))'(2'h3)) : ((Bit#(2))'(2'h1)));
        
        let x_6 = (procRqWait_a);
        let x_7 <- read_tag_a(x_3);
        when ((! (x_6)) && ((x_4 == (Bit#(2))'(2'h0)) || ((x_7 ==
        (((x_2).addr)[3:1])[2:2]) && ((x_4) < (x_5)))), noAction);
        let x_8 <- enq_rqToParent_a(Struct6 {addr : ((x_2).addr)[3:1], from :
        x_4, to : x_5, id : (Bit#(1))'(1'h0)});
        procRqWait_a <= (Bool)'(True);
        
    endrule
    
    rule upgRs_aa;
        let x_0 <- deq_fromParent_aa();
        when (! ((x_0).isRq), noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_aa(x_1);
        let x_3 <- write_cs_aa(Struct5 {addr : x_1, data : (x_0).to});
        let x_4 <- write_tag_aa(Struct8 {addr : x_1, data :
        ((x_0).addr)[2:2]});
        procRqWait_aa <= (Bool)'(False);
        if (x_2 == (Bit#(2))'(2'h0)) begin
            let x_5 <- write_line_aa(Struct9 {addr : x_1, data :
            (x_0).line});
            
        end else begin
        end
        
    endrule
    
    rule upgRs_a;
        let x_0 <- deq_fromParent_a();
        when (! ((x_0).isRq), noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_a(x_1);
        let x_3 <- write_cs_a(Struct5 {addr : x_1, data : (x_0).to});
        let x_4 <- write_tag_a(Struct8 {addr : x_1, data :
        ((x_0).addr)[2:2]});
        procRqWait_a <= (Bool)'(False);
        if (x_2 == (Bit#(2))'(2'h0)) begin
            let x_5 <- write_line_a(Struct9 {addr : x_1, data : (x_0).line});
            
        end else begin
        end
        
    endrule
    
    rule ld_aa;
        let x_0 = (procRqValid_aa);
        when (x_0, noAction);
        let x_1 = (procRqReplace_aa);
        when (! (x_1), noAction);
        let x_2 = (procRq_aa);
        when (! ((x_2).op), noAction);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_aa(x_3);
        when (x_4 == (((x_2).addr)[3:1])[2:2], noAction);
        let x_5 <- read_cs_aa(x_3);
        when (! ((x_5) < ((Bit#(2))'(2'h1))), noAction);
        let x_6 <- read_line_aa(x_3);
        procRqValid_aa <= (Bool)'(False);
        let x_7 <- enq_rsToProc_aa(Struct3 {data :
        (x_6)[((x_2).addr)[0:0]]});
        let x_8 <- deq_rqFromProc_aa();
        when (x_2 == x_8, noAction);
        
    endrule
    
    rule ld_a;
        let x_0 = (procRqValid_a);
        when (x_0, noAction);
        let x_1 = (procRqReplace_a);
        when (! (x_1), noAction);
        let x_2 = (procRq_a);
        when (! ((x_2).op), noAction);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_a(x_3);
        when (x_4 == (((x_2).addr)[3:1])[2:2], noAction);
        let x_5 <- read_cs_a(x_3);
        when (! ((x_5) < ((Bit#(2))'(2'h1))), noAction);
        let x_6 <- read_line_a(x_3);
        procRqValid_a <= (Bool)'(False);
        let x_7 <- enq_rsToProc_a(Struct3 {data : (x_6)[((x_2).addr)[0:0]]});
        
        let x_8 <- deq_rqFromProc_a();
        when (x_2 == x_8, noAction);
        
    endrule
    
    rule st_aa;
        let x_0 = (procRqValid_aa);
        when (x_0, noAction);
        let x_1 = (procRqReplace_aa);
        when (! (x_1), noAction);
        let x_2 = (procRq_aa);
        when ((x_2).op, noAction);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_aa(x_3);
        when (x_4 == (((x_2).addr)[3:1])[2:2], noAction);
        let x_5 <- read_cs_aa(x_3);
        when (x_5 == (Bit#(2))'(2'h3), noAction);
        let x_6 <- read_line_aa(x_3);
        procRqValid_aa <= (Bool)'(False);
        Bit#(1) x_7 = (((x_2).addr)[0:0]);
        let x_8 <- enq_rsToProc_aa(Struct3 {data : (Bit#(32))'(32'h0)});
        let x_9 <- write_line_aa(Struct9 {addr : x_3, data : update (x_6,
        x_7, (x_2).data)});
        let x_10 <- deq_rqFromProc_aa();
        when (x_2 == x_10, noAction);
        
    endrule
    
    rule st_a;
        let x_0 = (procRqValid_a);
        when (x_0, noAction);
        let x_1 = (procRqReplace_a);
        when (! (x_1), noAction);
        let x_2 = (procRq_a);
        when ((x_2).op, noAction);
        Bit#(2) x_3 = ((((x_2).addr)[3:1])[1:0]);
        let x_4 <- read_tag_a(x_3);
        when (x_4 == (((x_2).addr)[3:1])[2:2], noAction);
        let x_5 <- read_cs_a(x_3);
        when (x_5 == (Bit#(2))'(2'h3), noAction);
        let x_6 <- read_line_a(x_3);
        procRqValid_a <= (Bool)'(False);
        Bit#(1) x_7 = (((x_2).addr)[0:0]);
        let x_8 <- enq_rsToProc_a(Struct3 {data : (Bit#(32))'(32'h0)});
        let x_9 <- write_line_a(Struct9 {addr : x_3, data : update (x_6, x_7,
        (x_2).data)});
        let x_10 <- deq_rqFromProc_a();
        when (x_2 == x_10, noAction);
        
    endrule
    
    rule drop_aa;
        let x_0 <- deq_fromParent_aa();
        when ((x_0).isRq, noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_aa(x_1);
        let x_3 <- read_tag_aa(x_1);
        when ((! (((x_0).to) < (x_2))) || (! (x_3 == ((x_0).addr)[2:2])),
        noAction);
        
    endrule
    
    rule drop_a;
        let x_0 <- deq_fromParent_a();
        when ((x_0).isRq, noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_a(x_1);
        let x_3 <- read_tag_a(x_1);
        when ((! (((x_0).to) < (x_2))) || (! (x_3 == ((x_0).addr)[2:2])),
        noAction);
        
    endrule
    
    rule pProcess_aa;
        let x_0 <- deq_fromParent_aa();
        when ((x_0).isRq, noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_aa(x_1);
        let x_3 <- read_tag_aa(x_1);
        let x_4 <- read_line_aa(x_1);
        when ((((x_0).to) < (x_2)) && (x_3 == ((x_0).addr)[2:2]), noAction);
        
        let x_5 = (procRqValid_aa);
        let x_6 = (procRqWait_aa);
        let x_7 = (procRq_aa);
        when (! ((((x_5) && (! (x_6))) && (((x_7).addr)[3:1] == (x_0).addr))
        && ((((x_7).op) && (x_2 == (Bit#(2))'(2'h3))) || ((! ((x_7).op)) &&
        (x_2 == (Bit#(2))'(2'h1))))), noAction);
        let x_8 <- enq_rsToParent_aa(Struct4 {addr : (x_0).addr, to :
        (x_0).to, line : x_4, isVol : (Bool)'(False)});
        let x_9 <- write_cs_aa(Struct5 {addr : x_1, data : (x_0).to});
        
    endrule
    
    rule pProcess_a;
        let x_0 <- deq_fromParent_a();
        when ((x_0).isRq, noAction);
        Bit#(2) x_1 = (((x_0).addr)[1:0]);
        let x_2 <- read_cs_a(x_1);
        let x_3 <- read_tag_a(x_1);
        let x_4 <- read_line_a(x_1);
        when ((((x_0).to) < (x_2)) && (x_3 == ((x_0).addr)[2:2]), noAction);
        
        let x_5 = (procRqValid_a);
        let x_6 = (procRqWait_a);
        let x_7 = (procRq_a);
        when (! ((((x_5) && (! (x_6))) && (((x_7).addr)[3:1] == (x_0).addr))
        && ((((x_7).op) && (x_2 == (Bit#(2))'(2'h3))) || ((! ((x_7).op)) &&
        (x_2 == (Bit#(2))'(2'h1))))), noAction);
        let x_8 <- enq_rsToParent_a(Struct4 {addr : (x_0).addr, to :
        (x_0).to, line : x_4, isVol : (Bool)'(False)});
        let x_9 <- write_cs_a(Struct5 {addr : x_1, data : (x_0).to});
        
    endrule
    
    // No methods in this module
endmodule

interface Module16; 
endinterface


module mkModule16#(function Action enq_fromParent_a(Struct7 _),
  function Action enq_fromParent_aa(Struct7 _),
  function ActionValue#(Struct12) deq_toChild(),
  function ActionValue#(Struct4) deq_rsToParent_a(),
  function Action enq_rsFromChild(Struct11 _),
  function ActionValue#(Struct4) deq_rsToParent_aa(),
  function ActionValue#(Struct6) deq_rqToParent_a(),
  function Action enq_rqFromChild(Struct10 _),
  function ActionValue#(Struct6) deq_rqToParent_aa()) (Module16);
    
    
    rule rqFromCToP_aa;
        Bit#(1) x_0 = ((Bit#(1))'(1'h1));
        let x_1 <- deq_rqToParent_aa();
        let x_2 <- enq_rqFromChild(Struct10 {child : x_0, rq : x_1});
        
    endrule
    
    rule rqFromCToP_a;
        Bit#(1) x_0 = ((Bit#(1))'(1'h0));
        let x_1 <- deq_rqToParent_a();
        let x_2 <- enq_rqFromChild(Struct10 {child : x_0, rq : x_1});
        
    endrule
    
    rule rsFromCToP_aa;
        Bit#(1) x_0 = ((Bit#(1))'(1'h1));
        let x_1 <- deq_rsToParent_aa();
        let x_2 <- enq_rsFromChild(Struct11 {child : x_0, rs : x_1});
        
    endrule
    
    rule rsFromCToP_a;
        Bit#(1) x_0 = ((Bit#(1))'(1'h0));
        let x_1 <- deq_rsToParent_a();
        let x_2 <- enq_rsFromChild(Struct11 {child : x_0, rs : x_1});
        
    endrule
    
    rule fromPToC_aa;
        Bit#(1) x_0 = ((Bit#(1))'(1'h1));
        let x_1 <- deq_toChild();
        when (x_0 == (x_1).child, noAction);
        let x_2 <- enq_fromParent_aa((x_1).msg);
        
    endrule
    
    rule fromPToC_a;
        Bit#(1) x_0 = ((Bit#(1))'(1'h0));
        let x_1 <- deq_toChild();
        when (x_0 == (x_1).child, noAction);
        let x_2 <- enq_fromParent_a((x_1).msg);
        
    endrule
    
    // No methods in this module
endmodule

interface Module17; 
endinterface


module
  mkModule17#(function ActionValue#(Vector#(2, Bit#(32))) read_mline(Bit#(3) _),
  function ActionValue#(Struct10) deq_rqFromChild(),
  function Action write_mline(Struct15 _),
  function Action write_mcs(Struct14 _),
  function ActionValue#(Struct11) deq_rsFromChild(),
  function Action enq_toChild(Struct12 _),
  function ActionValue#(Vector#(2, Bit#(2))) read_mcs(Bit#(3) _),
  function ActionValue#(Struct10) firstElt_rqFromChild()) (Module17);
    Reg#(Bool) cRqValid <- mkReg(False);
    Reg#(Vector#(2, Bool)) cRqDirw <- mkReg(vec(False, False));
    
    rule missByState;
        let x_0 = (cRqValid);
        when (! (x_0), noAction);
        let x_1 <- firstElt_rqFromChild();
        Bit#(1) x_2 = ((x_1).child);
        Struct6 x_3 = ((x_1).rq);
        Bit#(3) x_4 = ((x_3).addr);
        let x_5 <- read_mcs(x_4);
        when (! (((x_3).from) < ((x_5)[x_2])), noAction);
        cRqValid <= (Bool)'(True);
        Vector#(2, Bool) x_6 = (vec((Bool)'(False), (Bool)'(False)));
        cRqDirw <= x_6;
        
    endrule
    
    rule dwnRq;
        let x_0 = (cRqValid);
        when (x_0, noAction);
        let x_1 <- firstElt_rqFromChild();
        Bit#(1) x_2 = ((x_1).child);
        Struct6 x_3 = ((x_1).rq);
        let x_4 <- read_mcs((x_3).addr);
        let x_5 = (cRqDirw);
        Struct13 x_6 = ((((! ((Struct13 {valid : (Bool)'(False), value :
        (Bit#(1))'(1'h0)}).valid)) && (! (x_2 == (Bit#(1))'(1'h0)))) && (! (!
        (((x_4)[(Bit#(1))'(1'h0)] == (Bit#(2))'(2'h3) ? ((Bit#(2))'(2'h0)) :
        ((x_4)[(Bit#(1))'(1'h0)] == (Bit#(2))'(2'h1) ? ((Bit#(2))'(2'h1)) :
        ((Bit#(2))'(2'h3)))) < ((x_3).to))))) && (!
        ((x_5)[(Bit#(1))'(1'h0)])) ? (Struct13 {valid : (Bool)'(True), value
        : (Bit#(1))'(1'h0)}) : (Struct13 {valid : (Bool)'(False), value :
        (Bit#(1))'(1'h0)}));
        when ((x_6).valid, noAction);
        Struct7 x_7 = (Struct7 {isRq : (Bool)'(True), addr : (x_3).addr, to :
        (x_3).to == (Bit#(2))'(2'h3) ? ((Bit#(2))'(2'h0)) : ((x_3).to ==
        (Bit#(2))'(2'h1) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h3))), line :
        (Vector#(2, Bit#(32)))'(vec(32'h0, 32'h0)), id : (Bit#(1))'(1'h0)});
        
        let x_8 <- enq_toChild(Struct12 {child : x_2, msg : x_7});
        
        Vector#(2, Bool) x_9 = (update (x_5, x_2, (Bool)'(True)));
        cRqDirw <= x_9;
        
    endrule
    
    rule dwnRs;
        let x_0 <- deq_rsFromChild();
        Bit#(1) x_1 = ((x_0).child);
        Struct4 x_2 = ((x_0).rs);
        Bit#(3) x_3 = ((x_2).addr);
        let x_4 <- read_mcs(x_3);
        Vector#(2, Bit#(2)) x_5 = (update (x_4, x_1, (x_2).to));
        let x_6 <- write_mcs(Struct14 {addr : x_3, data : x_5});
        let x_7 = (cRqDirw);
        Vector#(2, Bool) x_8 = (update (x_7, x_1, (Bool)'(False)));
        cRqDirw <= x_8;
        if ((x_4)[x_1] == (Bit#(2))'(2'h3)) begin
            let x_9 <- write_mline(Struct15 {addr : x_3, data : (x_2).line});
            
        end else begin
        end
        
    endrule
    
    rule deferred;
        let x_0 = (cRqValid);
        when (x_0, noAction);
        let x_1 <- deq_rqFromChild();
        Bit#(1) x_2 = ((x_1).child);
        Struct6 x_3 = ((x_1).rq);
        Bit#(3) x_4 = ((x_3).addr);
        let x_5 <- read_mcs(x_4);
        when (! (((x_3).from) < ((x_5)[x_2])), noAction);
        when (! (x_2 == (Bit#(1))'(1'h0)) ? ((! (((x_5)[(Bit#(1))'(1'h0)] ==
        (Bit#(2))'(2'h3) ? ((Bit#(2))'(2'h0)) : ((x_5)[(Bit#(1))'(1'h0)] ==
        (Bit#(2))'(2'h1) ? ((Bit#(2))'(2'h1)) : ((Bit#(2))'(2'h3)))) <
        ((x_3).to))) && ((Bool)'(True))) : ((Bool)'(True)), noAction);
        let x_6 <- read_mline(x_4);
        Struct7 x_7 = (Struct7 {isRq : (Bool)'(False), addr : (x_3).addr, to
        : (x_3).to, line : x_6, id : (x_3).id});
        let x_8 <- enq_toChild(Struct12 {child : x_2, msg : x_7});
        
        Vector#(2, Bit#(2)) x_9 = (update (x_5, x_2, (x_3).to));
        let x_10 <- write_mcs(Struct14 {addr : x_4, data : x_9});
        cRqValid <= (Bool)'(False);
        
    endrule
    
    // No methods in this module
endmodule


module mkTop#(function Action toHost_aa(Bit#(32) _),
  function Action toHost_a(Bit#(32) _)) (Empty);
    Module1 m1 <- mkModule1 ();
    Module2 m2 <- mkModule2 ();
    Module3 m3 <- mkModule3 ();
    Module4 m4 <- mkModule4 ();
    Module5 m5 <- mkModule5 ();
    Module6 m6 <- mkModule6 ();
    Module7 m7 <- mkModule7 ();
    Module8 m8 <- mkModule8 ();
    Module9 m9 <- mkModule9 ();
    Module10 m10 <- mkModule10 ();
    Module11 m11 <- mkModule11 ();
    Module12 m12 <- mkModule12 ();
    Module13 m13 <- mkModule13 (toHost_aa, m1.deq_rsToProc_aa,
    m1.enq_rqFromProc_aa);
    Module14 m14 <- mkModule14 (toHost_a, m1.deq_rsToProc_a,
    m1.enq_rqFromProc_a);
    Module15 m15 <- mkModule15 (m1.deq_rqFromProc_a, m1.enq_rsToProc_a,
    m1.deq_rqFromProc_aa, m1.enq_rsToProc_aa, m4.write_line_a,
    m3.write_tag_a, m7.deq_fromParent_a, m4.write_line_aa, m3.write_tag_aa,
    m7.deq_fromParent_aa, m5.enq_rqToParent_a, m5.enq_rqToParent_aa,
    m2.write_cs_a, m6.enq_rsToParent_a, m4.read_line_a, m2.write_cs_aa,
    m6.enq_rsToParent_aa, m4.read_line_aa, m2.read_cs_a, m3.read_tag_a,
    m1.firstElt_rqFromProc_a, m2.read_cs_aa, m3.read_tag_aa,
    m1.firstElt_rqFromProc_aa);
    Module16 m16 <- mkModule16 (m7.enq_fromParent_a, m7.enq_fromParent_aa,
    m10.deq_toChild, m6.deq_rsToParent_a, m9.enq_rsFromChild,
    m6.deq_rsToParent_aa, m5.deq_rqToParent_a, m8.enq_rqFromChild,
    m5.deq_rqToParent_aa);
    Module17 m17 <- mkModule17 (m11.read_mline, m8.deq_rqFromChild,
    m11.write_mline, m12.write_mcs, m9.deq_rsFromChild, m10.enq_toChild,
    m12.read_mcs, m8.firstElt_rqFromChild);
    
endmodule
