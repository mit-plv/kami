    //// Initialization logic

    Reg#(Bool) init <- mkReg(False);

    Reg#(Bool) llInitDone <- mkReg(False);
    Reg#(Bit#(10)) llInitIndex <- mkReg(0);

    Reg#(Bool) l1InitDone0 <- mkReg(False);
    Reg#(Bit#(8)) l1InitIndex0 <- mkReg(0);
    Reg#(Bool) l1InitDone1 <- mkReg(False);
    Reg#(Bit#(8)) l1InitIndex1 <- mkReg(0);
    Reg#(Bool) l1InitDone2 <- mkReg(False);
    Reg#(Bit#(8)) l1InitIndex2 <- mkReg(0);
    Reg#(Bool) l1InitDone3 <- mkReg(False);
    Reg#(Bit#(8)) l1InitIndex3 <- mkReg(0);

    function Struct22 llDefaultLine (Bit#(49) tagValue);
      return Struct22 { write: True,
                       addr: llInitIndex,
                       datain: Struct19 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 4'h0 }}};
    endfunction

    rule ll_info_do_init (!llInitDone);
        m1.putRq_infoRam_00_15 (llDefaultLine(15));
        m2.putRq_infoRam_00_14 (llDefaultLine(14));
        m3.putRq_infoRam_00_13 (llDefaultLine(13));
        m4.putRq_infoRam_00_12 (llDefaultLine(12));
        m5.putRq_infoRam_00_11 (llDefaultLine(11));
        m6.putRq_infoRam_00_10 (llDefaultLine(10));
        m7.putRq_infoRam_00_9 (llDefaultLine(9));
        m8.putRq_infoRam_00_8 (llDefaultLine(8));
        m9.putRq_infoRam_00_7 (llDefaultLine(7));
        m10.putRq_infoRam_00_6 (llDefaultLine(6));
        m11.putRq_infoRam_00_5 (llDefaultLine(5));
        m12.putRq_infoRam_00_4 (llDefaultLine(4));
        m13.putRq_infoRam_00_3 (llDefaultLine(3));
        m14.putRq_infoRam_00_2 (llDefaultLine(2));
        m15.putRq_infoRam_00_1 (llDefaultLine(1));
        m16.putRq_infoRam_00_0 (llDefaultLine(0));

        llInitIndex <= llInitIndex + 1;
        if (llInitIndex == maxBound) begin
            llInitDone <= True;
        end
    endrule

    function Struct29 l1DefaultLine (Bit#(51) tagValue, Bit#(8) index);
      return Struct29 { write: True,
                       addr: index,
                       datain: Struct26 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 4'h0 }}};
    endfunction

    rule l1_info_do_init_0 (!l1InitDone0);
        m19.putRq_infoRam_000_3 (l1DefaultLine(3, l1InitIndex0));
        m20.putRq_infoRam_000_2 (l1DefaultLine(2, l1InitIndex0));
        m21.putRq_infoRam_000_1 (l1DefaultLine(1, l1InitIndex0));
        m22.putRq_infoRam_000_0 (l1DefaultLine(0, l1InitIndex0));
        l1InitIndex0 <= l1InitIndex0 + 1;
        if (l1InitIndex0 == maxBound) begin
            l1InitDone0 <= True;
        end
    endrule

    rule l1_info_do_init_1 (!l1InitDone1);
        m30.putRq_infoRam_001_3 (l1DefaultLine(3, l1InitIndex1));
        m31.putRq_infoRam_001_2 (l1DefaultLine(2, l1InitIndex1));
        m32.putRq_infoRam_001_1 (l1DefaultLine(1, l1InitIndex1));
        m33.putRq_infoRam_001_0 (l1DefaultLine(0, l1InitIndex1));
        l1InitIndex1 <= l1InitIndex1 + 1;
        if (l1InitIndex1 == maxBound) begin
            l1InitDone1 <= True;
        end
    endrule

    rule l1_info_do_init_2 (!l1InitDone2);
        m41.putRq_infoRam_002_3 (l1DefaultLine(3, l1InitIndex2));
        m42.putRq_infoRam_002_2 (l1DefaultLine(2, l1InitIndex2));
        m43.putRq_infoRam_002_1 (l1DefaultLine(1, l1InitIndex2));
        m44.putRq_infoRam_002_0 (l1DefaultLine(0, l1InitIndex2));
        l1InitIndex2 <= l1InitIndex1 + 1;
        if (l1InitIndex2 == maxBound) begin
            l1InitDone2 <= True;
        end
    endrule

    rule l1_info_do_init_3 (!l1InitDone3);
        m52.putRq_infoRam_003_3 (l1DefaultLine(3, l1InitIndex3));
        m53.putRq_infoRam_003_2 (l1DefaultLine(2, l1InitIndex3));
        m54.putRq_infoRam_003_1 (l1DefaultLine(1, l1InitIndex3));
        m55.putRq_infoRam_003_0 (l1DefaultLine(0, l1InitIndex3));
        l1InitIndex3 <= l1InitIndex1 + 1;
        if (l1InitIndex3 == maxBound) begin
            l1InitDone3 <= True;
        end
    endrule

    rule init_done (!init && llInitDone &&
                    l1InitDone0 && l1InitDone1 && l1InitDone2 && l1InitDone3);
        init <= True;
    endrule

    function MemRqRs getMemRqRs (function Action enq_rq (Struct2 _),
                                 function ActionValue#(Struct2) deq_rs ());
        return interface MemRqRs;
                   method mem_enq_rq = enq_rq;
                   method mem_deq_rs = deq_rs;
               endinterface;
    endfunction

    Vector#(L1Num, MemRqRs) _l1Ifc = newVector();
    _l1Ifc[0] = getMemRqRs(m28.enq_fifo00000, m29.deq_fifo00002);
    _l1Ifc[1] = getMemRqRs(m39.enq_fifo00100, m40.deq_fifo00102);
    _l1Ifc[2] = getMemRqRs(m50.enq_fifo00200, m51.deq_fifo00202);
    _l1Ifc[3] = getMemRqRs(m61.enq_fifo00300, m62.deq_fifo00302);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_putRq = m17.putRq_dataRam_00;
        method dma_getRs = m17.getRs_dataRam_00;
    endinterface

    method Bool isInit ();
        return init;
    endmethod
