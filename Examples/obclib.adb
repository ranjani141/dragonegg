with interfaces;
use interfaces;
with Ada.Numerics.Generic_Elementary_Functions;


package body OBCLIB is

  function Bit_AND (value1, value2 : Unsigned_16) return Unsigned_16 is
  begin
   return(value1 and value2 );
  end Bit_AND;

   function Bit_OR (value1, value2 : Unsigned_16) return Unsigned_16 is
   begin
     return(value1 or value2 );
   end Bit_OR;

   function Bit_XOR (value1, value2 : Unsigned_16) return Unsigned_16 is
   begin
     return(value1 xor value2 );
   end Bit_XOR;

  function LBit_XOR (value1, value2 : Unsigned_32) return Unsigned_32 is
   begin
     return(value1 xor value2 );
   end LBit_XOR;

   function Bit_NOT (value: Unsigned_16) return Unsigned_16 is
   begin
      return(not value );
   end Bit_NOT;

  function Ushift_Left(value :Unsigned_16; amount:Unsigned_16) return  Unsigned_16 is
  begin
       return obclib.unsigned_16(Shift_Left(interfaces.unsigned_16(value), natural(amount)));
  end Ushift_Left;

  function Ushift_Right(value :Unsigned_16; amount:Unsigned_16) return  Unsigned_16 is
  begin
      return obclib.unsigned_16(Shift_Right(interfaces.unsigned_16(value), natural(amount)));
  end Ushift_Right;

end OBCLIB;
