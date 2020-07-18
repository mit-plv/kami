    //// Initialization logic

    Reg#(Bool) init <- mkReg(False);

    Reg#(Bool) llInitDone <- mkReg(False);
    Reg#(Bit#(10)) llInitIndex <- mkReg(0);

    Reg#(Bool) l2InitDone0 <- mkReg(False);
    Reg#(Bit#(9)) l2InitIndex0 <- mkReg(0);
    Reg#(Bool) l2InitDone1 <- mkReg(False);
    Reg#(Bit#(9)) l2InitIndex1 <- mkReg(0);

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
                                                         mesi_dir_sharers: 2'h0 }}};
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

    function Struct29 l2DefaultLine (Bit#(50) tagValue, Bit#(9) index);
      return Struct29 { write: True,
                       addr: index,
                       datain: Struct26 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 2'h0 }}};
    endfunction

    rule l2_info_do_init_0 (!l2InitDone0);
        m19.putRq_infoRam_000_7 (l2DefaultLine(7, l2InitIndex0));
        m20.putRq_infoRam_000_6 (l2DefaultLine(6, l2InitIndex0));
        m21.putRq_infoRam_000_5 (l2DefaultLine(5, l2InitIndex0));
        m22.putRq_infoRam_000_4 (l2DefaultLine(4, l2InitIndex0));
        m23.putRq_infoRam_000_3 (l2DefaultLine(3, l2InitIndex0));
        m24.putRq_infoRam_000_2 (l2DefaultLine(2, l2InitIndex0));
        m25.putRq_infoRam_000_1 (l2DefaultLine(1, l2InitIndex0));
        m26.putRq_infoRam_000_0 (l2DefaultLine(0, l2InitIndex0));

        l2InitIndex0 <= l2InitIndex0 + 1;
        if (l2InitIndex0 == maxBound) begin
            l2InitDone0 <= True;
        end
    endrule

    rule l2_info_do_init_1 (!l2InitDone1);
        m54.putRq_infoRam_001_7 (l2DefaultLine(7, l2InitIndex1));
        m55.putRq_infoRam_001_6 (l2DefaultLine(6, l2InitIndex1));
        m56.putRq_infoRam_001_5 (l2DefaultLine(5, l2InitIndex1));
        m57.putRq_infoRam_001_4 (l2DefaultLine(4, l2InitIndex1));
        m58.putRq_infoRam_001_3 (l2DefaultLine(3, l2InitIndex1));
        m59.putRq_infoRam_001_2 (l2DefaultLine(2, l2InitIndex1));
        m60.putRq_infoRam_001_1 (l2DefaultLine(1, l2InitIndex1));
        m61.putRq_infoRam_001_0 (l2DefaultLine(0, l2InitIndex1));

        l2InitIndex1 <= l2InitIndex1 + 1;
        if (l2InitIndex1 == maxBound) begin
            l2InitDone1 <= True;
        end
    endrule

    function Struct36 l1DefaultLine (Bit#(51) tagValue, Bit#(8) index);
      return Struct36 { write: True,
                       addr: index,
                       datain: Struct33 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 2'h0 }}};
    endfunction

    rule l1_info_do_init_0 (!l1InitDone0);
        m32.putRq_infoRam_0000_3 (l1DefaultLine(3, l1InitIndex0));
        m33.putRq_infoRam_0000_2 (l1DefaultLine(2, l1InitIndex0));
        m34.putRq_infoRam_0000_1 (l1DefaultLine(1, l1InitIndex0));
        m35.putRq_infoRam_0000_0 (l1DefaultLine(0, l1InitIndex0));
        l1InitIndex0 <= l1InitIndex0 + 1;
        if (l1InitIndex0 == maxBound) begin
            l1InitDone0 <= True;
        end
    endrule

    rule l1_info_do_init_1 (!l1InitDone1);
        m43.putRq_infoRam_0001_3 (l1DefaultLine(3, l1InitIndex1));
        m44.putRq_infoRam_0001_2 (l1DefaultLine(2, l1InitIndex1));
        m45.putRq_infoRam_0001_1 (l1DefaultLine(1, l1InitIndex1));
        m46.putRq_infoRam_0001_0 (l1DefaultLine(0, l1InitIndex1));
        l1InitIndex1 <= l1InitIndex1 + 1;
        if (l1InitIndex1 == maxBound) begin
            l1InitDone1 <= True;
        end
    endrule

    rule l1_info_do_init_2 (!l1InitDone2);
        m67.putRq_infoRam_0010_3 (l1DefaultLine(3, l1InitIndex2));
        m68.putRq_infoRam_0010_2 (l1DefaultLine(2, l1InitIndex2));
        m69.putRq_infoRam_0010_1 (l1DefaultLine(1, l1InitIndex2));
        m70.putRq_infoRam_0010_0 (l1DefaultLine(0, l1InitIndex2));
        l1InitIndex2 <= l1InitIndex1 + 1;
        if (l1InitIndex2 == maxBound) begin
            l1InitDone2 <= True;
        end
    endrule

    rule l1_info_do_init_3 (!l1InitDone3);
        m78.putRq_infoRam_0011_3 (l1DefaultLine(3, l1InitIndex3));
        m79.putRq_infoRam_0011_2 (l1DefaultLine(2, l1InitIndex3));
        m80.putRq_infoRam_0011_1 (l1DefaultLine(1, l1InitIndex3));
        m81.putRq_infoRam_0011_0 (l1DefaultLine(0, l1InitIndex3));
        l1InitIndex3 <= l1InitIndex1 + 1;
        if (l1InitIndex3 == maxBound) begin
            l1InitDone3 <= True;
        end
    endrule

    rule init_done (!init && llInitDone &&
                    l2InitDone0 && l2InitDone1 &&
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
    _l1Ifc[0] = getMemRqRs(m41.enq_fifo000000, m42.deq_fifo000002);
    _l1Ifc[1] = getMemRqRs(m52.enq_fifo000100, m53.deq_fifo000102);
    _l1Ifc[2] = getMemRqRs(m76.enq_fifo001000, m77.deq_fifo001002);
    _l1Ifc[3] = getMemRqRs(m87.enq_fifo001100, m88.deq_fifo001102);
    interface l1Ifc = _l1Ifc;

    interface DMA llDma;
        method dma_putRq = m17.putRq_dataRam_00;
        method dma_getRs = m17.getRs_dataRam_00;
    endinterface

    method Bool isInit ();
        return init;
    endmethod
