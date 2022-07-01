with Reals; use Reals;
with Ada.Numerics.Elementary_Functions; use Ada.Numerics.Elementary_Functions;

package body Heron with SPARK_Mode is
   
   function Heron (X : Float; N : Integer) return Float is
      Y : Float := 1.0;
   begin
   
      for i in 1 .. N loop
         Y := (Y + X/Y) / 2.0;
   
         pragma Loop_Invariant (Y >= 0.7);
         pragma Loop_Invariant (Y <= 1.8);
         pragma Loop_Invariant
           (abs(Real_Square_Root (FC.To_Big_Real(X)) - FC.To_Big_Real(Y))
            <=  To_Real(1) / (To_Real(2 ** (2 ** i))) + To_Real(3 * i) * (To_Real(1) / To_Real(8388608)));
   
      end loop;
   
      return Y;
   end Heron;
end Heron;
