import Vector::*;
import BuildVector::*;
import RWire::*;
import FIFO::*;

import Proc::*;

// Connectal interfaces

interface HostIndication;
    method Action msg_to_host1(Bit#(32) v);
    method Action msg_to_host2(Bit#(32) v);
    method Action msg_to_host3(Bit#(32) v);
    method Action msg_to_host4(Bit#(32) v);
endinterface

interface HostRequest;
    method Action start();
endinterface

// Connectal interfaces end

// A frontend wrapper to deal with the trigger from SW

interface FrontEnd;
    method Action toHost_a (Bit#(32) val);
    method Action toHost_aa (Bit#(32) val);
    method Action toHost_aaa (Bit#(32) val);
    method Action toHost_aaaa (Bit#(32) val);
    method Action start ();
endinterface

module mkFrontEnd#(HostIndication indication) (FrontEnd);
  
    Reg#(Bool) ready <- mkReg(False);

    method Action toHost_a (Bit#(32) val) if (ready);
	    indication.msg_to_host1(val);
    endmethod

    method Action toHost_aa (Bit#(32) val) if (ready);
	    indication.msg_to_host2(val);
    endmethod

    method Action toHost_aaa (Bit#(32) val) if (ready);
	    indication.msg_to_host3(val);
    endmethod

    method Action toHost_aaaa (Bit#(32) val) if (ready);
	    indication.msg_to_host4(val);
    endmethod

    method Action start();
        ready <= True;
    endmethod
endmodule

// A frontend wrapper ends

// The closed proc module for giving its synthesis boundary

interface Proc;
    method ActionValue#(Bit#(32)) read_toHost_aaaa;
    method ActionValue#(Bit#(32)) read_toHost_aaa;
    method ActionValue#(Bit#(32)) read_toHost_aa;
    method ActionValue#(Bit#(32)) read_toHost_a;
endinterface

(* synthesize *)
module mkProcWrapper (Proc);
    FIFO#(Bit#(32)) val1 <- mkSizedFIFO(2);
    FIFO#(Bit#(32)) val2 <- mkSizedFIFO(2);
    FIFO#(Bit#(32)) val3 <- mkSizedFIFO(2);
    FIFO#(Bit#(32)) val4 <- mkSizedFIFO(2);
    Empty proc <- mkProc (val4.enq, val3.enq, val2.enq, val1.enq);

    method ActionValue#(Bit#(32)) read_toHost_aaaa;
        val4.deq();
        return val4.first;
    endmethod

    method ActionValue#(Bit#(32)) read_toHost_aaa;
	val3.deq();
        return val3.first;
    endmethod

    method ActionValue#(Bit#(32)) read_toHost_aa;
	val2.deq();
        return val2.first;
    endmethod

    method ActionValue#(Bit#(32)) read_toHost_a;
	val1.deq();
        return val1.first;
    endmethod

endmodule

// The closed proc module ends
 
interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    FrontEnd frontEnd <- mkFrontEnd (indication);
    Proc proc <- mkProcWrapper ();

    (* fire_when_enabled *)
    rule to_frontend_aaaa;
        let val <- proc.read_toHost_aaaa ();
	frontEnd.toHost_aaaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aaa;
        let val <- proc.read_toHost_aaa ();
	frontEnd.toHost_aaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aa;
        let val <- proc.read_toHost_aa ();
	frontEnd.toHost_aa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_a;
        let val <- proc.read_toHost_a ();
	frontEnd.toHost_a(val);
    endrule

    interface HostRequest request;
        method Action start ();
	    frontEnd.start ();
	endmethod
    endinterface
endmodule

