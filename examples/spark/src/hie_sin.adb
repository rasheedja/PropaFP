with Ada.Numerics; use Ada.Numerics;

package body Hie_Sin with SPARK_Mode is

   procedure Multiply_Add (X, Y, Z : Float; Result : out Float) is
   begin
      Result := (X * Y + Z);
   end Multiply_Add;
     
   procedure My_Machine_Rounding (X : Float; Y : out Integer) is
   begin
      Y := Integer(X); -- RNA
   end My_Machine_Rounding;

   procedure Split_Veltkamp (X : Float; X_Hi, X_Lo : out Float) is
      M : constant Float := 0.5 + 2.0**(1 - Float'Machine_Mantissa / 2);
   begin
      X_Hi := X * M - (X * M - X);
      X_Lo := X - X_Hi;
   end Split_Veltkamp;
   
   procedure Reduce_Half_Pi (X : in out Float; Q : out Quadrant; R : out Integer) is
      K      : constant       := Pi / 2.0;
      --  Bits_N : constant       := 9;
      --  Bits_C : constant       := Float'Machine_Mantissa - Bits_N;
      C1     : constant Float := 1.57073974609375; -- Float'Leading_Part (K, Bits_C);
      C2     : constant Float := 0.0000565797090530395508; -- Float'Leading_Part (K - C1, Bits_C);
      C3     : constant Float := 0.000000000992088189377682284; -- Float'Leading_Part (K - C1 - C2, Bits_C);  
      C4     : constant Float := K - C1 - C2 - C3;
      N      : Float := (X / K);
   begin
      My_Machine_Rounding(N, R);
      --  R := Integer(N);
      
      X := (((X - Float(R) * C1) - Float(R) * C2) - Float(R) * C3) - Float(R) * C4;
      --  X := (X - Float(R) * K);
      Q := R mod 4; -- Return Integer (N) for specification
   end Reduce_Half_Pi;
      
   procedure Approx_Sin  (X : Float; Result : out Float) is
      --  Note: The reference tables named below for sine lists constants
      --  for sin((pi/4) * x) ~= x * P (x^2), in order to get sin (x),
      --  the constants have been adjusted by division of appropriate
      --  powers of (pi/4) ^ n, for n 1,3,5, etc.
      --  Sin_P  : constant Polynomial :=
      --       (1 => Float(Long_Float (-0.16666_65022)),
      --        2 => Float(Long_Float (0.83320_16396E-2)),
      --        3 => Float(Long_Float (-0.19501_81843E-3)));

      Sqrt_Epsilon_LF : constant Long_Float :=
        Sqrt_2 ** (1 - Long_Float'Machine_Mantissa); 

      G  : constant Float := X * X;
      
      -- Compute_Horner Manually
      H0 : constant Float := (-0.19501_81843E-3);
      H1 : Float; -- := (H0 * G + (0.83320_16396E-2));
      H2 : Float; -- := (H1 * G + (-0.16666_65022));
   begin
      Multiply_Add(H0, G, (0.83320_16396E-2), H1);
      Multiply_Add(H1, G, (-0.16666_65022), H2);

      if abs X <= Float(Long_Float (Sqrt_Epsilon_LF)) then
         Result := X;
      else
         Result := (X * (H2 * G) + X);
      end if;
   end Approx_Sin;

   procedure Approx_Cos (X : Float; Result : out Float) is
      --  Note: The reference tables named below for cosine lists
      --  constants for cos((pi/4) * x) ~= P (x^2), in order to get
      --  cos (x), the constants have been adjusted by division of
      --  appropriate  powers of (pi/4) ^ n, for n 0,2,4,6 etc.
      --  Cos_P : constant Polynomial :=
      --    (0 => (0.99999_99999),
      --     1 => (-0.49999_99957),
      --     2 => (0.41666_61323E-1),
      --     3 => (-0.13888_52915E-2),
      --     4 => (0.24372_67909E-4));
      
      G  : constant Float := X * X;
      
      H0 : constant Float := (0.24372_67909E-4);	
      H1 : Float; -- := (H0 * G + (-0.13888_52915E-2));
      H2 : Float; -- := (H1 * G + (0.41666_61323E-1));
      H3 : Float; -- := (H2 * G + (-0.49999_99957));
      H4 : Float; -- := (H3 * G + (0.99999_99999));
   begin
      Multiply_Add(H0, G, (-0.13888_52915E-2), H1);
      Multiply_Add(H1, G, (0.41666_61323E-1), H2);
      Multiply_Add(H2, G, (-0.49999_99957), H3);
      Multiply_Add(H3, G, (0.99999_99999), H4);

      Result := H4;
   end Approx_Cos;

   procedure Sin (X : Float; FinalResult : out Float) is
      --  Math based implementation using Hart constants
      Y      : Float := (if X < 0.0 then -X else X);
      --  Y : Float;
      Q      : Quadrant;
      R      : Integer;
      Result : Float;
   begin
      Reduce_Half_Pi (Y, Q, R);
   
      if Q = 0 or Q = 2 then
         Approx_Sin (Y, Result);
      else -- Q = 1 or Q = 3
         Approx_Cos (Y, Result);
      end if;
   
      if X < 0.0 then
         FinalResult := (if Q >= 2 then Result else -Result);
      else
         FinalResult := (if Q >= 2 then -Result else Result);
      end if;
   end Sin;

end Hie_Sin;
