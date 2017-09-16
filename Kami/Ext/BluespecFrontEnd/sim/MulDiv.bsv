function Bit#(n) multiply_unsigned( Bit#(n) a, Bit#(n) b );
    UInt#(n) a_uint = unpack(a);
    UInt#(n) b_uint = unpack(b);
    UInt#(TAdd#(n,n)) product_uint = zeroExtend(a_uint) * zeroExtend(b_uint);
    return pack( truncate(product_uint) );
endfunction

function Bit#(n) multiply_signed( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Int#(n) b_int = unpack(b);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) * signExtend(b_int);
    return pack( truncate(product_int) );
endfunction

function Bit#(n) multiply_signed_unsigned( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Bit#(TSub#(n,1)) b_trunc = truncate(b);
    Bit#(n) b_uint = {0, b_trunc};
    Int#(n) b_int = unpack(b_uint);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) * signExtend(b_int);
    return pack( truncate(product_int) );
endfunction

function Bit#(n) divide_unsigned( Bit#(n) a, Bit#(n) b );
    UInt#(n) a_uint = unpack(a);
    UInt#(n) b_uint = unpack(b);
    UInt#(TAdd#(n,n)) product_uint = zeroExtend(a_uint) / zeroExtend(b_uint);
    return pack( truncate(product_uint) );
endfunction

function Bit#(n) divide_signed( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Int#(n) b_int = unpack(b);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) / signExtend(b_int);
    return pack( truncate(product_int) );
endfunction

function Bit#(n) divide_signed_unsigned( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Bit#(TSub#(n,1)) b_trunc = truncate(b);
    Bit#(n) b_uint = {0, b_trunc};
    Int#(n) b_int = unpack(b_uint);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) / signExtend(b_int);
    return pack( truncate(product_int) );
endfunction

function Bit#(n) remainder_unsigned( Bit#(n) a, Bit#(n) b );
    UInt#(n) a_uint = unpack(a);
    UInt#(n) b_uint = unpack(b);
    UInt#(TAdd#(n,n)) product_uint = zeroExtend(a_uint) % zeroExtend(b_uint);
    return pack( truncate(product_uint) );
endfunction

function Bit#(n) remainder_signed( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Int#(n) b_int = unpack(b);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) % signExtend(b_int);
    return pack( truncate(product_int) );
endfunction

function Bit#(n) remainder_signed_unsigned( Bit#(n) a, Bit#(n) b );
    Int#(n) a_int = unpack(a);
    Bit#(TSub#(n,1)) b_trunc = truncate(b);
    Bit#(n) b_uint = {0, b_trunc};
    Int#(n) b_int = unpack(b_uint);
    Int#(TAdd#(n,n)) product_int = signExtend(a_int) % signExtend(b_int);
    return pack( truncate(product_int) );
endfunction
