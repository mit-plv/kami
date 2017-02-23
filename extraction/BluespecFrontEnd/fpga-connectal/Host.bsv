import Vector::*;
import BuildVector::*;
import RWire::*;

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
    method Bit#(32) read_toHost_aaaa;
    method Bit#(32) read_toHost_aaa;
    method Bit#(32) read_toHost_aa;
    method Bit#(32) read_toHost_a;
endinterface

(* synthesize *)
module mkProc (Proc);
    Wire#(Bit#(32)) val1 <- mkWire();
    Wire#(Bit#(32)) val2 <- mkWire();
    Wire#(Bit#(32)) val3 <- mkWire();
    Wire#(Bit#(32)) val4 <- mkWire();
    Empty procTop <- mkTop (val4._write, val3._write, val2._write, val1._write);

    method Bit#(32) read_toHost_aaaa;
        return val4;
    endmethod

    method Bit#(32) read_toHost_aaa;
        return val3;
    endmethod

    method Bit#(32) read_toHost_aa;
        return val2;
    endmethod

    method Bit#(32) read_toHost_a;
        return val1;
    endmethod

endmodule

// The closed proc module ends
 
interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    FrontEnd frontEnd <- mkFrontEnd (indication);
    Proc proc <- mkProc ();

    (* fire_when_enabled *)
    rule to_frontend_aaaa;
        let val = proc.read_toHost_aaaa ();
	frontEnd.toHost_aaaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aaa;
        let val = proc.read_toHost_aaa ();
	frontEnd.toHost_aaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aa;
        let val = proc.read_toHost_aa ();
	frontEnd.toHost_aa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_a;
        let val = proc.read_toHost_a ();
	frontEnd.toHost_a(val);
    endrule

    interface HostRequest request;
        method Action start ();
	    frontEnd.start ();
	endmethod
    endinterface
endmodule

