with obclib;
Use  obclib;

package test6 is

Type F32Array1by3 is array (short_integer range 1..4) of float32;

procedure CrossProduct (Vec1, Vec2 : in F32Array1by3; Vec3 : out F32Array1by3);
                       
                      
end test6;
