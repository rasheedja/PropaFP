pragma Ada_2022;

with Reals; use Reals;

with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;


package Heron with SPARK_Mode is

   function Heron (X : Float; N : Integer) Return Float with
     Pre => X >= 0.5 and X <= 2.0 and N >= 1 and N <= 5, --and Eps = 2.0 ** (-23),
     Post =>
       abs(Real_Square_Root (FC.To_Big_Real(X)) - FC.To_Big_Real(Heron'Result))
         <=  To_Real(1) / (To_Real(2 ** (2 ** N))) + To_Real(3 * N) * (To_Real(1) / To_Real(8388608));

end Heron;
