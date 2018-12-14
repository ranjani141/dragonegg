
package OBCLIB is

     type Unsigned_16 is mod 2**16;
     type Unsigned_32 is mod 2**32;
     type float32 is digits 6;
     type float64 is digits 15;

     function Bit_AND (value1, value2 : Unsigned_16) return Unsigned_16;
     function Bit_OR (value1, value2 : Unsigned_16) return Unsigned_16;
     function Bit_XOR (value1, value2 : Unsigned_16) return Unsigned_16;
     function LBit_XOR (value1, value2 : Unsigned_32) return Unsigned_32;
     function Bit_NOT (value: Unsigned_16) return Unsigned_16;
     function Ushift_Left(value :Unsigned_16; amount:Unsigned_16) return  Unsigned_16;
     function Ushift_Right(value :Unsigned_16; amount:Unsigned_16) return  Unsigned_16;

end OBCLIB;
