import Vector::*;
import BuildVector::*;

typedef struct { Bit#(4) addr; Bool op; Bit#(32) data;  } Struct1 deriving(Eq, Bits);
typedef struct { Bit#(32) data;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(7) opcode; Bit#(5) reg_; Bit#(4) addr; Bit#(32) value; Bit#(32) inst;  } Struct3 deriving(Eq, Bits);

interface Module1;
    method Action enq_rqFromProc_aa (Struct1 x_0);
    method ActionValue#(Struct1) deq_rqFromProc_aa ();
endinterface

module mkModule1 (Module1);
    Reg#(Vector#(4, Struct1)) elt_rqFromProc_aa <- mkReg(vec(Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}));
    Reg#(Bit#(2)) enqP_rqFromProc_aa <- mkReg(2'h0);
    Reg#(Bit#(2)) deqP_rqFromProc_aa <- mkReg(2'h0);
    Reg#(Bool) empty_rqFromProc_aa <- mkReg(True);
    Reg#(Bool) full_rqFromProc_aa <- mkReg(False);
    // No rules in this module
    
    method Action enq_rqFromProc_aa (Struct1 x_0);
        let x_1 = (full_rqFromProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_aa);
        let x_3 = (enqP_rqFromProc_aa);
        let x_4 = (deqP_rqFromProc_aa);
        elt_rqFromProc_aa <= update (x_2, x_3, x_0);
        empty_rqFromProc_aa <= (Bool)'(False);
        Bit#(2) x_5 = ((x_3) + ((Bit#(2))'(2'h1)));
        full_rqFromProc_aa <= x_4 == x_5;
        enqP_rqFromProc_aa <= x_5;
        
    endmethod
    
    method ActionValue#(Struct1) deq_rqFromProc_aa ();
        let x_1 = (empty_rqFromProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_aa);
        let x_3 = (enqP_rqFromProc_aa);
        let x_4 = (deqP_rqFromProc_aa);
        full_rqFromProc_aa <= (Bool)'(False);
        Bit#(2) x_5 = ((x_4) + ((Bit#(2))'(2'h1)));
        empty_rqFromProc_aa <= x_3 == x_5;
        deqP_rqFromProc_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module2;
    method Action enq_rsToProc_aa (Struct2 x_0);
    method ActionValue#(Struct2) deq_rsToProc_aa ();
endinterface

module mkModule2 (Module2);
    Reg#(Vector#(4, Struct2)) elt_rsToProc_aa <- mkReg(vec(Struct2 {data: 32'h0}, Struct2 {data: 32'h0}, Struct2 {data: 32'h0}, Struct2 {data: 32'h0}));
    Reg#(Bit#(2)) enqP_rsToProc_aa <- mkReg(2'h0);
    Reg#(Bit#(2)) deqP_rsToProc_aa <- mkReg(2'h0);
    Reg#(Bool) empty_rsToProc_aa <- mkReg(True);
    Reg#(Bool) full_rsToProc_aa <- mkReg(False);
    // No rules in this module
    
    method Action enq_rsToProc_aa (Struct2 x_0);
        let x_1 = (full_rsToProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_aa);
        let x_3 = (enqP_rsToProc_aa);
        let x_4 = (deqP_rsToProc_aa);
        elt_rsToProc_aa <= update (x_2, x_3, x_0);
        empty_rsToProc_aa <= (Bool)'(False);
        Bit#(2) x_5 = ((x_3) + ((Bit#(2))'(2'h1)));
        full_rsToProc_aa <= x_4 == x_5;
        enqP_rsToProc_aa <= x_5;
        
    endmethod
    
    method ActionValue#(Struct2) deq_rsToProc_aa ();
        let x_1 = (empty_rsToProc_aa);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_aa);
        let x_3 = (enqP_rsToProc_aa);
        let x_4 = (deqP_rsToProc_aa);
        full_rsToProc_aa <= (Bool)'(False);
        Bit#(2) x_5 = ((x_4) + ((Bit#(2))'(2'h1)));
        empty_rsToProc_aa <= x_3 == x_5;
        deqP_rsToProc_aa <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module3;
    method Action enq_rqFromProc_a (Struct1 x_0);
    method ActionValue#(Struct1) deq_rqFromProc_a ();
endinterface

module mkModule3 (Module3);
    Reg#(Vector#(4, Struct1)) elt_rqFromProc_a <- mkReg(vec(Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}, Struct1 {addr: 4'h0, op: False, data: 32'h0}));
    Reg#(Bit#(2)) enqP_rqFromProc_a <- mkReg(2'h0);
    Reg#(Bit#(2)) deqP_rqFromProc_a <- mkReg(2'h0);
    Reg#(Bool) empty_rqFromProc_a <- mkReg(True);
    Reg#(Bool) full_rqFromProc_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_rqFromProc_a (Struct1 x_0);
        let x_1 = (full_rqFromProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_a);
        let x_3 = (enqP_rqFromProc_a);
        let x_4 = (deqP_rqFromProc_a);
        elt_rqFromProc_a <= update (x_2, x_3, x_0);
        empty_rqFromProc_a <= (Bool)'(False);
        Bit#(2) x_5 = ((x_3) + ((Bit#(2))'(2'h1)));
        full_rqFromProc_a <= x_4 == x_5;
        enqP_rqFromProc_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct1) deq_rqFromProc_a ();
        let x_1 = (empty_rqFromProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rqFromProc_a);
        let x_3 = (enqP_rqFromProc_a);
        let x_4 = (deqP_rqFromProc_a);
        full_rqFromProc_a <= (Bool)'(False);
        Bit#(2) x_5 = ((x_4) + ((Bit#(2))'(2'h1)));
        empty_rqFromProc_a <= x_3 == x_5;
        deqP_rqFromProc_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module4;
    method Action enq_rsToProc_a (Struct2 x_0);
    method ActionValue#(Struct2) deq_rsToProc_a ();
endinterface

module mkModule4 (Module4);
    Reg#(Vector#(4, Struct2)) elt_rsToProc_a <- mkReg(vec(Struct2 {data: 32'h0}, Struct2 {data: 32'h0}, Struct2 {data: 32'h0}, Struct2 {data: 32'h0}));
    Reg#(Bit#(2)) enqP_rsToProc_a <- mkReg(2'h0);
    Reg#(Bit#(2)) deqP_rsToProc_a <- mkReg(2'h0);
    Reg#(Bool) empty_rsToProc_a <- mkReg(True);
    Reg#(Bool) full_rsToProc_a <- mkReg(False);
    // No rules in this module
    
    method Action enq_rsToProc_a (Struct2 x_0);
        let x_1 = (full_rsToProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_a);
        let x_3 = (enqP_rsToProc_a);
        let x_4 = (deqP_rsToProc_a);
        elt_rsToProc_a <= update (x_2, x_3, x_0);
        empty_rsToProc_a <= (Bool)'(False);
        Bit#(2) x_5 = ((x_3) + ((Bit#(2))'(2'h1)));
        full_rsToProc_a <= x_4 == x_5;
        enqP_rsToProc_a <= x_5;
        
    endmethod
    
    method ActionValue#(Struct2) deq_rsToProc_a ();
        let x_1 = (empty_rsToProc_a);
        when (! (x_1), noAction);
        let x_2 = (elt_rsToProc_a);
        let x_3 = (enqP_rsToProc_a);
        let x_4 = (deqP_rsToProc_a);
        full_rsToProc_a <= (Bool)'(False);
        Bit#(2) x_5 = ((x_4) + ((Bit#(2))'(2'h1)));
        empty_rsToProc_a <= x_3 == x_5;
        deqP_rsToProc_a <= x_5;
        return (x_2)[x_4];
    endmethod
    
endmodule

interface Module5;
    method ActionValue#(Struct2) exec_aa (Struct1 x_0);
    method ActionValue#(Struct2) exec_a (Struct1 x_0);
endinterface

module mkModule5 (Module5);
    Reg#(Vector#(16, Bit#(32))) mem <- mkReg(vec(32'ha00a93, 32'h1505b63, 32'h100493, 32'ha8313, 32'h48413, 32'h48393, 32'h8382b3, 32'h148493, 32'h40393, 32'h28413, 32'h931c63, 32'h28008, 32'h60006f, 32'h100293, 32'h1a0006f, 32'h13));
    
    // No rules in this module
    
    method ActionValue#(Struct2) exec_aa (Struct1 x_0);
        let x_4 = ?;
        if (! ((x_0).op)) begin
            let x_1 = (mem);
            Bit#(32) x_2 = ((x_1)[(x_0).addr]);
            x_4 = Struct2 {data : x_2};
        end else begin
            let x_3 = (mem);
            mem <= update (x_3, (x_0).addr, (x_0).data);
            x_4 = Struct2 {data : (Bit#(32))'(32'h0)};
        end
        return x_4;
    endmethod
    
    method ActionValue#(Struct2) exec_a (Struct1 x_0);
        let x_4 = ?;
        if (! ((x_0).op)) begin
            let x_1 = (mem);
            Bit#(32) x_2 = ((x_1)[(x_0).addr]);
            x_4 = Struct2 {data : x_2};
        end else begin
            let x_3 = (mem);
            mem <= update (x_3, (x_0).addr, (x_0).data);
            x_4 = Struct2 {data : (Bit#(32))'(32'h0)};
        end
        return x_4;
    endmethod
    
endmodule

interface Module6; 
endinterface


module mkModule6#(function Action toHost_aa(Bit#(32) _),
  function ActionValue#(Struct2) deq_rsToProc_aa(),
  function Action enq_rqFromProc_aa(Struct1 _)) (Module6);
    Reg#(Bit#(4)) pc_aa <- mkReg(4'h0);
    Reg#(Vector#(32, Bit#(32))) rf_aa <- mkReg(vec(32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0));
    Reg#(Bool) fetch_aa <- mkReg(True);
    Reg#(Bit#(32)) fetched_aa <- mkReg(32'h0);
    Reg#(Bool) fetchStall_aa <- mkReg(False);
    Reg#(Bool) stall_aa <- mkReg(False);
    
    rule reqInstFetch_aa;
        let x_0 = (fetch_aa);
        when (x_0, noAction);
        let x_1 = (fetchStall_aa);
        when (! (x_1), noAction);
        let x_2 = (pc_aa);
        let x_3 <- enq_rqFromProc_aa(Struct1 {addr : x_2, op :
        (Bool)'(False), data : (Bit#(32))'(32'h0)});
        fetchStall_aa <= (Bool)'(True);
        
    endrule
    
    rule repInstFetch_aa;
        let x_0 = (fetch_aa);
        when (x_0, noAction);
        let x_1 <- deq_rsToProc_aa();
        Bit#(32) x_2 = ((x_1).data);
        fetched_aa <= x_2;
        fetch_aa <= (Bool)'(False);
        fetchStall_aa <= (Bool)'(False);
        
    endrule
    
    rule reqLd_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 = (stall_aa);
        when (! (x_1), noAction);
        let x_2 = (rf_aa);
        let x_3 = (fetched_aa);
        Struct3 x_4 = ((x_3)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_3)[6:0], reg_ : (x_3)[11:7], addr :
        (truncate((x_2)[(x_3)[19:15]])) + (truncate((x_3)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(x_3)[19:15]])) +
        (truncate({((x_3)[31:25]),((x_3)[11:7])})), value :
        (x_2)[(x_3)[24:20]], inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_2)[(x_3)[19:15]], inst : x_3}) :
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_3}))));
        when ((x_4).opcode == (Bit#(7))'(7'h3), noAction);
        let x_5 <- enq_rqFromProc_aa(Struct1 {addr : (x_4).addr, op :
        (Bool)'(False), data : (Bit#(32))'(32'h0)});
        stall_aa <= (Bool)'(True);
        
    endrule
    
    rule reqSt_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 = (stall_aa);
        when (! (x_1), noAction);
        let x_2 = (rf_aa);
        let x_3 = (fetched_aa);
        Struct3 x_4 = ((x_3)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_3)[6:0], reg_ : (x_3)[11:7], addr :
        (truncate((x_2)[(x_3)[19:15]])) + (truncate((x_3)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(x_3)[19:15]])) +
        (truncate({((x_3)[31:25]),((x_3)[11:7])})), value :
        (x_2)[(x_3)[24:20]], inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_2)[(x_3)[19:15]], inst : x_3}) :
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_3}))));
        when ((x_4).opcode == (Bit#(7))'(7'h23), noAction);
        let x_5 <- enq_rqFromProc_aa(Struct1 {addr : (x_4).addr, op :
        (Bool)'(True), data : (x_4).value});
        stall_aa <= (Bool)'(True);
        
    endrule
    
    rule repLd_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 <- deq_rsToProc_aa();
        let x_2 = (pc_aa);
        let x_3 = (rf_aa);
        let x_4 = (fetched_aa);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h3), noAction);
        rf_aa <= update (x_3, (x_5).reg_, (x_1).data);
        stall_aa <= (Bool)'(False);
        pc_aa <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_aa <= (Bool)'(True);
        
    endrule
    
    rule repSt_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 <- deq_rsToProc_aa();
        let x_2 = (pc_aa);
        let x_3 = (rf_aa);
        let x_4 = (fetched_aa);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h23), noAction);
        stall_aa <= (Bool)'(False);
        pc_aa <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_aa <= (Bool)'(True);
        
    endrule
    
    rule execToHost_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 = (stall_aa);
        when (! (x_1), noAction);
        let x_2 = (pc_aa);
        let x_3 = (rf_aa);
        let x_4 = (fetched_aa);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h8), noAction);
        let x_6 <- toHost_aa((x_5).value);
        pc_aa <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_aa <= (Bool)'(True);
        
    endrule
    
    rule execNm_aa;
        let x_0 = (fetch_aa);
        when (! (x_0), noAction);
        let x_1 = (stall_aa);
        when (! (x_1), noAction);
        let x_2 = (pc_aa);
        let x_3 = (rf_aa);
        let x_4 = (fetched_aa);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when (! ((((x_5).opcode == (Bit#(7))'(7'h3)) || ((x_5).opcode ==
        (Bit#(7))'(7'h23))) || ((x_5).opcode == (Bit#(7))'(7'h8))),
        noAction);
        rf_aa <= (x_5).opcode == (Bit#(7))'(7'h33) ? (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) + ((x_3)[((x_5).inst)[24:20]]))) :
        (((x_5).inst)[31:25] == (Bit#(7))'(7'h20) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) -
        ((x_3)[((x_5).inst)[24:20]]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) << (((x_3)[((x_5).inst)[24:20]])[4:0])))
        : (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) >>
        (((x_3)[((x_5).inst)[24:20]])[4:0]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h20) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) >> (((x_3)[((x_5).inst)[24:20]])[4:0])))
        : (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) |
        ((x_3)[((x_5).inst)[24:20]]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) & ((x_3)[((x_5).inst)[24:20]]))) :
        (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) ^
        ((x_3)[((x_5).inst)[24:20]]))) : (x_3))))))))) : ((x_5).opcode ==
        (Bit#(7))'(7'h13) ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        (update (x_3, ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) +
        (zeroExtend(((x_5).inst)[31:20])))) : (x_3)) : (x_3));
        pc_aa <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_aa <= (Bool)'(True);
        
    endrule
    
    // No methods in this module
endmodule

interface Module7; 
endinterface


module mkModule7#(function Action toHost_a(Bit#(32) _),
  function ActionValue#(Struct2) deq_rsToProc_a(),
  function Action enq_rqFromProc_a(Struct1 _)) (Module7);
    Reg#(Bit#(4)) pc_a <- mkReg(4'h0);
    Reg#(Vector#(32, Bit#(32))) rf_a <- mkReg(vec(32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0, 32'h0));
    Reg#(Bool) fetch_a <- mkReg(True);
    Reg#(Bit#(32)) fetched_a <- mkReg(32'h0);
    Reg#(Bool) fetchStall_a <- mkReg(False);
    Reg#(Bool) stall_a <- mkReg(False);
    
    rule reqInstFetch_a;
        let x_0 = (fetch_a);
        when (x_0, noAction);
        let x_1 = (fetchStall_a);
        when (! (x_1), noAction);
        let x_2 = (pc_a);
        let x_3 <- enq_rqFromProc_a(Struct1 {addr : x_2, op : (Bool)'(False),
        data : (Bit#(32))'(32'h0)});
        fetchStall_a <= (Bool)'(True);
        
    endrule
    
    rule repInstFetch_a;
        let x_0 = (fetch_a);
        when (x_0, noAction);
        let x_1 <- deq_rsToProc_a();
        Bit#(32) x_2 = ((x_1).data);
        fetched_a <= x_2;
        fetch_a <= (Bool)'(False);
        fetchStall_a <= (Bool)'(False);
        
    endrule
    
    rule reqLd_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 = (stall_a);
        when (! (x_1), noAction);
        let x_2 = (rf_a);
        let x_3 = (fetched_a);
        Struct3 x_4 = ((x_3)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_3)[6:0], reg_ : (x_3)[11:7], addr :
        (truncate((x_2)[(x_3)[19:15]])) + (truncate((x_3)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(x_3)[19:15]])) +
        (truncate({((x_3)[31:25]),((x_3)[11:7])})), value :
        (x_2)[(x_3)[24:20]], inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_2)[(x_3)[19:15]], inst : x_3}) :
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_3}))));
        when ((x_4).opcode == (Bit#(7))'(7'h3), noAction);
        let x_5 <- enq_rqFromProc_a(Struct1 {addr : (x_4).addr, op :
        (Bool)'(False), data : (Bit#(32))'(32'h0)});
        stall_a <= (Bool)'(True);
        
    endrule
    
    rule reqSt_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 = (stall_a);
        when (! (x_1), noAction);
        let x_2 = (rf_a);
        let x_3 = (fetched_a);
        Struct3 x_4 = ((x_3)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_3)[6:0], reg_ : (x_3)[11:7], addr :
        (truncate((x_2)[(x_3)[19:15]])) + (truncate((x_3)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_2)[(x_3)[19:15]])) +
        (truncate({((x_3)[31:25]),((x_3)[11:7])})), value :
        (x_2)[(x_3)[24:20]], inst : x_3}) : ((x_3)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_2)[(x_3)[19:15]], inst : x_3}) :
        (Struct3 {opcode : (x_3)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_3}))));
        when ((x_4).opcode == (Bit#(7))'(7'h23), noAction);
        let x_5 <- enq_rqFromProc_a(Struct1 {addr : (x_4).addr, op :
        (Bool)'(True), data : (x_4).value});
        stall_a <= (Bool)'(True);
        
    endrule
    
    rule repLd_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 <- deq_rsToProc_a();
        let x_2 = (pc_a);
        let x_3 = (rf_a);
        let x_4 = (fetched_a);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h3), noAction);
        rf_a <= update (x_3, (x_5).reg_, (x_1).data);
        stall_a <= (Bool)'(False);
        pc_a <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_a <= (Bool)'(True);
        
    endrule
    
    rule repSt_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 <- deq_rsToProc_a();
        let x_2 = (pc_a);
        let x_3 = (rf_a);
        let x_4 = (fetched_a);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h23), noAction);
        stall_a <= (Bool)'(False);
        pc_a <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_a <= (Bool)'(True);
        
    endrule
    
    rule execToHost_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 = (stall_a);
        when (! (x_1), noAction);
        let x_2 = (pc_a);
        let x_3 = (rf_a);
        let x_4 = (fetched_a);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when ((x_5).opcode == (Bit#(7))'(7'h8), noAction);
        let x_6 <- toHost_a((x_5).value);
        pc_a <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_a <= (Bool)'(True);
        
    endrule
    
    rule execNm_a;
        let x_0 = (fetch_a);
        when (! (x_0), noAction);
        let x_1 = (stall_a);
        when (! (x_1), noAction);
        let x_2 = (pc_a);
        let x_3 = (rf_a);
        let x_4 = (fetched_a);
        Struct3 x_5 = ((x_4)[6:0] == (Bit#(7))'(7'h3) ? (Struct3 {opcode :
        (x_4)[6:0], reg_ : (x_4)[11:7], addr :
        (truncate((x_3)[(x_4)[19:15]])) + (truncate((x_4)[31:20])), value :
        (Bit#(32))'(32'h0), inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h23) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (truncate((x_3)[(x_4)[19:15]])) +
        (truncate({((x_4)[31:25]),((x_4)[11:7])})), value :
        (x_3)[(x_4)[24:20]], inst : x_4}) : ((x_4)[6:0] == (Bit#(7))'(7'h8) ?
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (x_3)[(x_4)[19:15]], inst : x_4}) :
        (Struct3 {opcode : (x_4)[6:0], reg_ : (Bit#(5))'(5'h0), addr :
        (Bit#(4))'(4'h0), value : (Bit#(32))'(32'h0), inst : x_4}))));
        when (! ((((x_5).opcode == (Bit#(7))'(7'h3)) || ((x_5).opcode ==
        (Bit#(7))'(7'h23))) || ((x_5).opcode == (Bit#(7))'(7'h8))),
        noAction);
        rf_a <= (x_5).opcode == (Bit#(7))'(7'h33) ? (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) + ((x_3)[((x_5).inst)[24:20]]))) :
        (((x_5).inst)[31:25] == (Bit#(7))'(7'h20) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) -
        ((x_3)[((x_5).inst)[24:20]]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) << (((x_3)[((x_5).inst)[24:20]])[4:0])))
        : (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) >>
        (((x_3)[((x_5).inst)[24:20]])[4:0]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h20) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) >> (((x_3)[((x_5).inst)[24:20]])[4:0])))
        : (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) |
        ((x_3)[((x_5).inst)[24:20]]))) : (((x_5).inst)[31:25] ==
        (Bit#(7))'(7'h0) ? (update (x_3, ((x_5).inst)[11:7],
        ((x_3)[((x_5).inst)[19:15]]) & ((x_3)[((x_5).inst)[24:20]]))) :
        (((x_5).inst)[31:25] == (Bit#(7))'(7'h0) ? (update (x_3,
        ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) ^
        ((x_3)[((x_5).inst)[24:20]]))) : (x_3))))))))) : ((x_5).opcode ==
        (Bit#(7))'(7'h13) ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        (update (x_3, ((x_5).inst)[11:7], ((x_3)[((x_5).inst)[19:15]]) +
        (zeroExtend(((x_5).inst)[31:20])))) : (x_3)) : (x_3));
        pc_a <= (x_5).opcode == (Bit#(7))'(7'h6f) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[19:12])}),({(((x_5).inst)[20:20]),(((x_5).inst)[30:21])})})))
        : ((x_5).opcode == (Bit#(7))'(7'h67) ? (((x_2) +
        (truncate((x_3)[((x_5).inst)[19:15]]))) +
        (truncate(((x_5).inst)[31:20]))) : ((x_5).opcode == (Bit#(7))'(7'h63)
        ? (((x_5).inst)[14:12] == (Bit#(3))'(3'h0) ?
        ((x_3)[((x_5).inst)[19:15]] == (x_3)[((x_5).inst)[24:20]] ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h1) ? (! ((x_3)[((x_5).inst)[19:15]] ==
        (x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h4) ? (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]]) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : (((x_5).inst)[14:12] ==
        (Bit#(3))'(3'h5) ? (! (((x_3)[((x_5).inst)[19:15]]) <
        ((x_3)[((x_5).inst)[24:20]])) ? ((x_2) +
        (truncate({({(((x_5).inst)[31:31]),(((x_5).inst)[7:7])}),({(((x_5).inst)[30:25]),(((x_5).inst)[11:8])})})))
        : ((x_2) + ((Bit#(4))'(4'h1)))) : ((x_2) + ((Bit#(4))'(4'h1))))))) :
        ((x_2) + ((Bit#(4))'(4'h1)))));
        fetch_a <= (Bool)'(True);
        
    endrule
    
    // No methods in this module
endmodule

interface Module8; 
endinterface


module mkModule8#(function Action enq_rsToProc_aa(Struct2 _),
  function ActionValue#(Struct2) exec_aa(Struct1 _),
  function ActionValue#(Struct1) deq_rqFromProc_aa()) (Module8);
    
    
    rule processLd_aa;
        let x_0 <- deq_rqFromProc_aa();
        when (! ((x_0).op), noAction);
        let x_1 <- exec_aa(x_0);
        let x_2 <- enq_rsToProc_aa(x_1);
        
    endrule
    
    rule processSt_aa;
        let x_0 <- deq_rqFromProc_aa();
        when ((x_0).op, noAction);
        let x_1 <- exec_aa(x_0);
        let x_2 <- enq_rsToProc_aa(x_1);
        
    endrule
    
    // No methods in this module
endmodule

interface Module9; 
endinterface


module mkModule9#(function Action enq_rsToProc_a(Struct2 _),
  function ActionValue#(Struct2) exec_a(Struct1 _),
  function ActionValue#(Struct1) deq_rqFromProc_a()) (Module9);
    
    
    rule processLd_a;
        let x_0 <- deq_rqFromProc_a();
        when (! ((x_0).op), noAction);
        let x_1 <- exec_a(x_0);
        let x_2 <- enq_rsToProc_a(x_1);
        
    endrule
    
    rule processSt_a;
        let x_0 <- deq_rqFromProc_a();
        when ((x_0).op, noAction);
        let x_1 <- exec_a(x_0);
        let x_2 <- enq_rsToProc_a(x_1);
        
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
    Module6 m6 <- mkModule6 (toHost_aa, m2.deq_rsToProc_aa,
    m1.enq_rqFromProc_aa);
    Module7 m7 <- mkModule7 (toHost_a, m4.deq_rsToProc_a,
    m3.enq_rqFromProc_a);
    Module8 m8 <- mkModule8 (m2.enq_rsToProc_aa, m5.exec_aa,
    m1.deq_rqFromProc_aa);
    Module9 m9 <- mkModule9 (m4.enq_rsToProc_a, m5.exec_a,
    m3.deq_rqFromProc_a);
    
endmodule
