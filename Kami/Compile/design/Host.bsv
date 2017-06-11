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

interface Proc;
    (* always_ready *)
    method Bit#(32) toHost_aaaa;
    (* always_ready *)
    method Bool toHost_aaaa_en; 
    (* always_ready *)
    method Action toHost_aaaa_g(); 

    (* always_ready *)
    method Bit#(32) toHost_aaa;
    (* always_ready *)
    method Bool toHost_aaa_en; 
    (* always_ready *)
    method Action toHost_aaa_g(); 

    (* always_ready *)
    method Bit#(32) toHost_aa;
    (* always_ready *)
    method Bool toHost_aa_en; 
    (* always_ready *)
    method Action toHost_aa_g(); 

    (* always_ready *)
    method Bit#(32) toHost_a;
    (* always_ready *)
    method Bool toHost_a_en; 
    (* always_ready *)
    method Action toHost_a_g(); 
endinterface


import "BVI" top =
module mkProc(Proc);
  default_clock clk(CLK) <- exposeCurrentClock;
  default_reset rst (RESET_N) clocked_by(clk) <- exposeCurrentReset;

  method toHost_aaaa__arg toHost_aaaa();
  method toHost_aaa__arg toHost_aaa();
  method toHost_aa__arg toHost_aa();
  method toHost_a__arg toHost_a();

  method toHost_aaaa__en toHost_aaaa_en();
  method toHost_aaa__en toHost_aaa_en();
  method toHost_aa__en toHost_aa_en();
  method toHost_a__en toHost_a_en();

  method toHost_aaaa_g() enable(toHost_aaaa__g);
  method toHost_aaa_g() enable(toHost_aaa__g);
  method toHost_aa_g() enable(toHost_aa__g);
  method toHost_a_g() enable(toHost_a__g);

  schedule (toHost_aaaa, toHost_aaa, toHost_aa, toHost_a,
            toHost_aaaa_en, toHost_aaa_en, toHost_aa_en, toHost_a_en,
            toHost_aaaa_g, toHost_aaa_g, toHost_aa_g, toHost_a_g) CF
           (toHost_aaaa, toHost_aaa, toHost_aa, toHost_a,
            toHost_aaaa_en, toHost_aaa_en, toHost_aa_en, toHost_a_en,
            toHost_aaaa_g, toHost_aaa_g, toHost_aa_g, toHost_a_g);

  path(toHost_aaaa_g, toHost_aaaa);
  path(toHost_aaaa_g, toHost_aaaa_en);

  path(toHost_aaa_g, toHost_aaa);
  path(toHost_aaa_g, toHost_aaa_en);

  path(toHost_aa_g, toHost_aa);
  path(toHost_aa_g, toHost_aa_en);

  path(toHost_a_g, toHost_a);
  path(toHost_a_g, toHost_a_en);
endmodule
 
interface Host;
    interface HostRequest request;
endinterface

module mkHost#(HostIndication indication) (Host);
    FrontEnd frontEnd <- mkFrontEnd (indication);
    Proc proc <- mkProc ();

    (* fire_when_enabled *)
    rule to_frontend_aaaa(proc.toHost_aaaa_en);
        let val = proc.toHost_aaaa ();
	frontEnd.toHost_aaaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aaa(proc.toHost_aaa_en);
        let val = proc.toHost_aaa ();
	frontEnd.toHost_aaa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_aa(proc.toHost_aa_en);
        let val = proc.toHost_aa ();
	frontEnd.toHost_aa(val);
    endrule

    (* fire_when_enabled *)
    rule to_frontend_a(proc.toHost_a_en);
        let val = proc.toHost_a ();
	frontEnd.toHost_a(val);
    endrule

    (* fire_when_enabled *)
    rule setReady;
      proc.toHost_aaaa_g;
      proc.toHost_aaa_g;
      proc.toHost_aa_g;
      proc.toHost_a_g;
    endrule

    interface HostRequest request;
        method Action start ();
	    frontEnd.start ();
	endmethod
    endinterface
endmodule

