with obclib;
Use  obclib;

package test4 is

--  Type F32Array1by3 is array (short_integer range 1..3) of float32;
--  Type F32Array1by3 is array (short_integer range 1..3) of Integer;
   Type F32Array1by3 is array (1..5) of Integer;
--  A : in F32Array1by3; 
procedure test41(  C : in Integer; O : out Integer );
                      
end test4;
