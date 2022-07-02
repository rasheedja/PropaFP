pragma Ada_2022;

with Reals; use Reals;

with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

package Taylor_Sin with SPARK_Mode is
   
   function Taylor_Sin (X : Float) return Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post => 
       abs(Real_Sin(FC.To_Big_Real(X)) - FC.To_Big_Real(Taylor_Sin'Result)) <= To_Real(25889) / To_Real(100000000);
                                                                                     
   function Taylor_Sin_Double (X : Long_Float) return Long_Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       abs(Real_Sin(FLC.To_Big_Real(X)) - FLC.To_Big_Real(Taylor_Sin_Double'Result)) <= To_Real(258872) / To_Real(1000000000);
   
   procedure Taylor_Sin_P (X : Float; R : out Float) with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       FC.To_Big_Real(R) >= To_Real(-48) / To_Real(100) and -- Important to add bounds on outputs for functions/procedures that rely on this
     FC.To_Big_Real(R) <= To_Real(48) / To_Real(100) and
     abs(Real_Sin(FC.To_Big_Real(X)) - FC.To_Big_Real(R)) <= To_Real(25889) / To_Real(100000000);
   
   function SinSin ( X : Float) return Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       abs(Real_Sin(Real_Sin(FC.To_Big_Real(X))) - FC.To_Big_Real(SinSin'Result)) <= To_Real(51778) / To_Real(100000000);
   
   function Taylor_Sin_Plus (X : Float) return Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       abs(Real_Sin(FC.To_Big_Real(X)) - FC.To_Big_Real(Taylor_Sin_Plus'Result)) <= To_Real(25889) / To_Real(100000000);
   
   function Taylor_Sin_Swap (X : Float) return Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       abs(Real_Sin(FC.To_Big_Real(X)) - FC.To_Big_Real(Taylor_Sin_Swap'Result)) >= To_Real(25889) / To_Real(100000000);
   
   function Taylor_Sin_Tight (X : Float) return Float with
     Pre => X >= -0.5 and X <= 0.5,
     Post =>
       abs(Real_Sin(FC.To_Big_Real(X)) - FC.To_Big_Real(Taylor_Sin_Tight'Result)) <= To_Real(25887) / To_Real(100000000);                                                                     -- 0.00000001769513 (E3 + E2)
end Taylor_Sin;
