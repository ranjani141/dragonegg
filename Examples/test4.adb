package body test4 is

--c : short_integer;
--A : F32Array1by3;
--  A : in F32Array1by3; 
procedure test41(C : in Integer; O : out Integer ) is
I : Integer;
--  C : short_integer;
AB : F32Array1by3;
--  A : array (1..12) of Integer;

begin
   if C > 3 then
      I := 1;
      --  O := AB(2);
   else
      I := 2;
      --  O := AB(1);
   end if;
   --  O := 3;
   O := AB(I);
end test41;
	
end test4;	
