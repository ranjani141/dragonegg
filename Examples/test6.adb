with library;

package body test6 is
  
  
procedure CrossProduct (Vec1, Vec2 : in F32Array1by3; Vec3 : out F32Array1by3) is
     begin
     
            Vec3(1) := Vec1(2) * Vec2(3) - Vec1(3) * Vec2(2);
--            Vec3(2) := Vec1(3) * Vec2(1) - Vec1(1) * Vec2(3);
--            Vec3(3) := Vec1(1) * Vec2(2) - Vec1(2) * Vec2(1);

     end CrossProduct; 

 	
end test6;	
