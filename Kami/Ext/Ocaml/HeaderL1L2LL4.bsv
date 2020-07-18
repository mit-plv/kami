import Vector::*;
import BuildVector::*;
import FIFO::*;
import FIFOF::*;
import RWBramCore::*;
import SpecialFIFOs::*;

typedef 4 L1Num;

interface MemRqRs;
    method Action mem_enq_rq (Struct2 rq);
    method ActionValue#(Struct2) mem_deq_rs ();
endinterface

interface DMA;
    method Action dma_putRq (Struct21 x_0);
    method ActionValue#(Vector#(4, Bit#(64))) dma_getRs ();
endinterface

interface CC;
    interface Vector#(L1Num, MemRqRs) l1Ifc;
    interface DMA llDma;
    method Bool isInit ();
endinterface

