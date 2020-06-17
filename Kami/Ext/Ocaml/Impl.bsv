    //// Initialization logic

    Reg#(Bool) init <- mkReg(False);

    Reg#(Bool) llInitDone <- mkReg(False);
    Reg#(Bit#(10)) llInitIndex <- mkReg(0);

    Reg#(Bool) l2InitDone0 <- mkReg(False);
    Reg#(Bit#(8)) l2InitIndex0 <- mkReg(0);
    Reg#(Bool) l2InitDone1 <- mkReg(False);
    Reg#(Bit#(8)) l2InitIndex1 <- mkReg(0);

    Reg#(Bool) l1InitDone0 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex0 <- mkReg(0);
    Reg#(Bool) l1InitDone1 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex1 <- mkReg(0);
    Reg#(Bool) l1InitDone2 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex2 <- mkReg(0);
    Reg#(Bool) l1InitDone3 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex3 <- mkReg(0);
    Reg#(Bool) l1InitDone4 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex4 <- mkReg(0);
    Reg#(Bool) l1InitDone5 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex5 <- mkReg(0);
    Reg#(Bool) l1InitDone6 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex6 <- mkReg(0);
    Reg#(Bool) l1InitDone7 <- mkReg(False);
    Reg#(Bit#(6)) l1InitIndex7 <- mkReg(0);

    function Struct22 llDefaultLine (Bit#(51) tagValue);
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
        if (llInitIndex == 10'b1111111111) begin
            $display ("-- ll: initialization completed");
            llInitDone <= True;
        end
    endrule

    function Struct29 l2DefaultLine (Bit#(53) tagValue, Bit#(8) index);
      return Struct29 { write: True,
                       addr: index,
                       datain: Struct26 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 4'h0 }}};
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
        if (l2InitIndex0 == 8'b11111111) begin
            $display ("-- l2_0: initialization completed");
            l2InitDone0 <= True;
        end
    endrule

    rule l2_info_do_init_1 (!l2InitDone1);
        m76.putRq_infoRam_001_7 (l2DefaultLine(7, l2InitIndex1));
        m77.putRq_infoRam_001_6 (l2DefaultLine(6, l2InitIndex1));
        m78.putRq_infoRam_001_5 (l2DefaultLine(5, l2InitIndex1));
        m79.putRq_infoRam_001_4 (l2DefaultLine(4, l2InitIndex1));
        m80.putRq_infoRam_001_3 (l2DefaultLine(3, l2InitIndex1));
        m81.putRq_infoRam_001_2 (l2DefaultLine(2, l2InitIndex1));
        m82.putRq_infoRam_001_1 (l2DefaultLine(1, l2InitIndex1));
        m83.putRq_infoRam_001_0 (l2DefaultLine(0, l2InitIndex1));

        l2InitIndex1 <= l2InitIndex1 + 1;
        if (l2InitIndex1 == 8'b11111111) begin
            $display ("-- l2_1: initialization completed");
            l2InitDone1 <= True;
        end
    endrule

    function Struct36 l1DefaultLine (Bit#(55) tagValue, Bit#(6) index);
      return Struct36 { write: True,
                       addr: index,
                       datain: Struct33 { tag: tagValue,
                                         value: Struct4 { mesi_owned: False,
                                                         mesi_status: 3'h1,
                                                         mesi_dir_st: 3'h1,
                                                         mesi_dir_sharers: 4'h0 }}};
    endfunction

    rule l1_info_do_init_0 (!l1InitDone0);
        m32.putRq_infoRam_0000_3 (l1DefaultLine(3, l1InitIndex0));
        m33.putRq_infoRam_0000_2 (l1DefaultLine(2, l1InitIndex0));
        m34.putRq_infoRam_0000_1 (l1DefaultLine(1, l1InitIndex0));
        m35.putRq_infoRam_0000_0 (l1DefaultLine(0, l1InitIndex0));
        l1InitIndex0 <= l1InitIndex0 + 1;
        if (l1InitIndex0 == 6'b111111) begin
            $display ("-- l1_0: initialization completed");
            l1InitDone0 <= True;
        end
    endrule

    rule l1_info_do_init_1 (!l1InitDone1);
        m43.putRq_infoRam_0001_3 (l1DefaultLine(3, l1InitIndex1));
        m44.putRq_infoRam_0001_2 (l1DefaultLine(2, l1InitIndex1));
        m45.putRq_infoRam_0001_1 (l1DefaultLine(1, l1InitIndex1));
        m46.putRq_infoRam_0001_0 (l1DefaultLine(0, l1InitIndex1));
        l1InitIndex1 <= l1InitIndex1 + 1;
        if (l1InitIndex1 == 6'b111111) begin
            $display ("-- l1_1: initialization completed");
            l1InitDone1 <= True;
        end
    endrule

    rule l1_info_do_init_2 (!l1InitDone2);
        m54.putRq_infoRam_0002_3 (l1DefaultLine(3, l1InitIndex2));
        m55.putRq_infoRam_0002_2 (l1DefaultLine(2, l1InitIndex2));
        m56.putRq_infoRam_0002_1 (l1DefaultLine(1, l1InitIndex2));
        m57.putRq_infoRam_0002_0 (l1DefaultLine(0, l1InitIndex2));
        l1InitIndex2 <= l1InitIndex1 + 1;
        if (l1InitIndex2 == 6'b111111) begin
            $display ("-- l1_2: initialization completed");
            l1InitDone2 <= True;
        end
    endrule

    rule l1_info_do_init_3 (!l1InitDone3);
        m65.putRq_infoRam_0003_3 (l1DefaultLine(3, l1InitIndex3));
        m66.putRq_infoRam_0003_2 (l1DefaultLine(2, l1InitIndex3));
        m67.putRq_infoRam_0003_1 (l1DefaultLine(1, l1InitIndex3));
        m68.putRq_infoRam_0003_0 (l1DefaultLine(0, l1InitIndex3));
        l1InitIndex3 <= l1InitIndex1 + 1;
        if (l1InitIndex3 == 6'b111111) begin
            $display ("-- l1_3: initialization completed");
            l1InitDone3 <= True;
        end
    endrule

    rule l1_info_do_init_4 (!l1InitDone4);
        m89.putRq_infoRam_0010_3 (l1DefaultLine(3, l1InitIndex4));
        m90.putRq_infoRam_0010_2 (l1DefaultLine(2, l1InitIndex4));
        m91.putRq_infoRam_0010_1 (l1DefaultLine(1, l1InitIndex4));
        m92.putRq_infoRam_0010_0 (l1DefaultLine(0, l1InitIndex4));
        l1InitIndex4 <= l1InitIndex4 + 1;
        if (l1InitIndex4 == 6'b111111) begin
            $display ("-- l1_4: initialization completed");
            l1InitDone4 <= True;
        end
    endrule

    rule l1_info_do_init_5 (!l1InitDone5);
        m100.putRq_infoRam_0011_3 (l1DefaultLine(3, l1InitIndex5));
        m101.putRq_infoRam_0011_2 (l1DefaultLine(2, l1InitIndex5));
        m102.putRq_infoRam_0011_1 (l1DefaultLine(1, l1InitIndex5));
        m103.putRq_infoRam_0011_0 (l1DefaultLine(0, l1InitIndex5));
        l1InitIndex5 <= l1InitIndex5 + 1;
        if (l1InitIndex5 == 6'b111111) begin
            $display ("-- l1_5: initialization completed");
            l1InitDone5 <= True;
        end
    endrule

    rule l1_info_do_init_6 (!l1InitDone6);
        m111.putRq_infoRam_0012_3 (l1DefaultLine(3, l1InitIndex6));
        m112.putRq_infoRam_0012_2 (l1DefaultLine(2, l1InitIndex6));
        m113.putRq_infoRam_0012_1 (l1DefaultLine(1, l1InitIndex6));
        m114.putRq_infoRam_0012_0 (l1DefaultLine(0, l1InitIndex6));
        l1InitIndex6 <= l1InitIndex6 + 1;
        if (l1InitIndex6 == 6'b111111) begin
            $display ("-- l1_6: initialization completed");
            l1InitDone6 <= True;
        end
    endrule

    rule l1_info_do_init_7 (!l1InitDone7);
        m122.putRq_infoRam_0013_3 (l1DefaultLine(3, l1InitIndex7));
        m123.putRq_infoRam_0013_2 (l1DefaultLine(2, l1InitIndex7));
        m124.putRq_infoRam_0013_1 (l1DefaultLine(1, l1InitIndex7));
        m125.putRq_infoRam_0013_0 (l1DefaultLine(0, l1InitIndex7));
        l1InitIndex7 <= l1InitIndex7 + 1;
        if (l1InitIndex7 == 6'b111111) begin
            $display ("-- l1_7: initialization completed");
            l1InitDone7 <= True;
        end
    endrule

    rule init_done (!init && llInitDone &&
                    l2InitDone0 && l2InitDone1 &&
                    l1InitDone0 && l1InitDone1 && l1InitDone2 && l1InitDone3 &&
                    l1InitDone4 && l1InitDone5 && l1InitDone6 && l1InitDone7);
        $display ("-- ALL: initialization completed");
        init <= True;
    endrule

    method Bool isInit ();
        return init;
    endmethod

    //// Interface
    method mem_enq_rq_0 = m41.enq_fifo000000;
    method mem_deq_rs_0 = m42.deq_fifo000002;
    method mem_enq_rq_1 = m52.enq_fifo000100;
    method mem_deq_rs_1 = m53.deq_fifo000102;
    method mem_enq_rq_2 = m63.enq_fifo000200;
    method mem_deq_rs_2 = m64.deq_fifo000202;
    method mem_enq_rq_3 = m74.enq_fifo000300;
    method mem_deq_rs_3 = m75.deq_fifo000302;

    method mem_enq_rq_4 = m98.enq_fifo001000;
    method mem_deq_rs_4 = m99.deq_fifo001002;
    method mem_enq_rq_5 = m109.enq_fifo001100;
    method mem_deq_rs_5 = m110.deq_fifo001102;
    method mem_enq_rq_6 = m120.enq_fifo001200;
    method mem_deq_rs_6 = m121.deq_fifo001202;
    method mem_enq_rq_7 = m131.enq_fifo001300;
    method mem_deq_rs_7 = m132.deq_fifo001302;
