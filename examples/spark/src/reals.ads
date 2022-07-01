
pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

package Reals
  with SPARK_Mode
is
   --  package Integer_Convert is new Signed_Conversions(Integer);
   package FC is new Float_Conversions(Float);
   package FLC is new Float_Conversions(Long_Float);

   function Real_Square_Root (A : Big_Real) return Big_Real
     with
       Pre => A >= To_Real(0),
       Post =>
         Real_Square_Root'Result >= To_Real(0) and -- Sqrt_positive
         Real_Square_Root'Result * Real_Square_Root'Result = A; -- Sqrt_square
                                                                                             
   function Real_Pi return Big_Real
     with
     Post =>
       Real_Pi'Result >= 7074237752028440 / 2251799813685248 and -- Pi_double_precision_bounds
       Real_Pi'Result <= 7074237752028441 / 2251799813685248; -- Pi_double_precision_bounds

   function Real_Cos (A : Big_Real) return Big_Real
     with
       Post =>
         abs(Real_Cos'Result) <= To_Real(1) and -- Cos_le_one
         (if A = To_Real(0) then (Real_Cos'Result = To_Real(1))) and -- Cos_0
         (if A = Real_Pi then Real_Cos'Result = To_Real(-1)) and -- Cos_pi
         (if A = (To_Real(1) / To_Real(2)) * Real_Pi then Real_Cos'Result = To_Real(0)); -- Cos_pi2

   function Real_Sin (A : Big_Real) return Big_Real
     with
       
       Post =>
         abs(Real_Sin'Result) <= To_Real(1) and -- Sin_le
         (if A = To_Real(0) then Real_Sin'Result = To_Real(0)) and -- Sin_0
         (if A = Real_Pi then Real_Sin'Result = To_Real(0)) and -- Sin_pi
         (if A = (To_Real(1) / To_Real(2)) * Real_Pi then Real_Sin'Result = To_Real(1)); -- Sin_pi2

end Reals;
