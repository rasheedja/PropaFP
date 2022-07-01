pragma Ada_2022;

with Ada.Numerics; use Ada.Numerics;
with Reals; use Reals;

with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

package Hie_Sin with SPARK_Mode is

   subtype Quadrant is Integer range 0 .. 3;
   
   Max_Red_Trig_Arg : constant := 0.26 * Ada.Numerics.Pi;
   Half_Pi          : constant := Ada.Numerics.Pi / 2.0;
   Sqrt_2           : constant := 1.41421_35623_73095_04880_16887_24209_69807_85696;

   type Polynomial is array (Natural range <>) of Float;

   procedure Multiply_Add (X, Y, Z : Float; Result : out Float) with
     Pre => 
       (-3.0 <= X and X <= 3.0) and
     (-3.0 <= Y and Y <= 3.0) and
     (-3.0 <= Z and Z <= 3.0),
     Post =>
       (-12.0 <= Result and Result <= 12.0) and
     Result = X * Y + Z;

   procedure My_Machine_Rounding (X : Float; Y : out Integer) with
     Pre =>
       (0.0 <= X and X <= 511.0),
     Post =>
       (0 <= Y and Y <= 511) and
     FC.To_Big_Real(X) - To_Real(Y) >= To_Real(-500000001) / To_Real(1000000000) and
     FC.To_Big_Real(X) - To_Real(Y) <= To_Real(500000001) / To_Real(1000000000);
   
   procedure Split_Veltkamp (X : Float; X_Hi, X_Lo : out Float)
     with 
       Pre => (-100000.0 <= X and X <= 100000.0),
       Post => X = X_Hi + X_Lo;

   procedure Reduce_Half_Pi (X : in out Float; Q : out Quadrant; R : out Integer)
     with Pre  => X >= 0.0 and X <= 802.0,
     Post => 
       R >= 0 and R <= 511 and
     FC.To_Big_Real(X'Old / (Pi / 2.0)) - To_Real(R) >= To_Real(-500000001) / To_Real(1000000000) and
     FC.To_Big_Real(X'Old / (Pi / 2.0)) - To_Real(R) <= To_Real(500000001) / To_Real(1000000000) and
     Q = R mod 4 and 
     X >= -Max_Red_Trig_Arg and X <= Max_Red_Trig_Arg and
     (FC.To_Big_Real(X) - (FC.To_Big_Real(X'Old) - (To_Real(R) * Real_Pi / FC.To_Big_Real(2.0)))) >= To_Real(-18) / To_Real(100000) and
     (FC.To_Big_Real(X) - (FC.To_Big_Real(X'Old) - (To_Real(R) * Real_Pi / FC.To_Big_Real(2.0)))) <= To_Real(18) / To_Real(100000);

   procedure Approx_Sin  (X : Float; Result : out Float)
     with Pre  => X >= -Max_Red_Trig_Arg and X <= Max_Red_Trig_Arg,
     Post => Result >= -1.0 and Result <= 1.0 and
     (FC.To_Big_Real(Result) - Real_Sin(FC.To_Big_Real(X))) >= To_Real(-58) / To_Real(1000000000) and
     (FC.To_Big_Real(Result) - Real_Sin(FC.To_Big_Real(X))) <= To_Real(58) / To_Real(1000000000);
   
   procedure Approx_Cos (X : Float; Result : out Float)
     with Pre  => X >= -Max_Red_Trig_Arg and X <= Max_Red_Trig_Arg,
     Post => Result >= -1.0 and Result <= 1.0 and
     (FC.To_Big_Real(Result) - Real_Cos(FC.To_Big_Real(X))) >= To_Real(-14) / To_Real(100000000) and
     (FC.To_Big_Real(Result) - Real_Cos(FC.To_Big_Real(X))) <= To_Real(14) / To_Real(100000000);

   procedure Sin (X : Float; FinalResult : out Float)
     with Pre => X >= -802.0 and X <= 802.0, Export, Convention => C, External_Name => "sinf",
     Post =>
       (FC.To_Big_Real(FinalResult) - Real_Sin(FC.To_Big_Real(X))) >= To_Real(-19) / To_Real(100000) and 
       (FC.To_Big_Real(FinalResult) - Real_Sin(FC.To_Big_Real(X))) <= To_Real(19) / To_Real(100000); 

end Hie_Sin;
