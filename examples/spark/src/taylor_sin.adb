package body Taylor_Sin with SPARK_Mode is

   function Taylor_Sin (X : Float) return Float is (X - ((X * X * X) / 6.0));

   function Taylor_Sin_Double (X : Long_Float) return Long_Float is (X - ((X * X * X) / 6.0));
   -- fun SinSin X
   --   return (Taylor_Sin (Taylor_Sin X))

   procedure Taylor_Sin_P (X : Float; R : out Float) is
   begin
      R := X - ((X * X * X) / 6.0);
   end Taylor_Sin_P;


   function SinSin (X : Float) return Float is
      OneSin : Float;
      TwoSin : Float;
   begin
      Taylor_Sin_P(X, OneSin);
      Taylor_Sin_P(OneSin, TwoSin);
      return TwoSin;
   end SinSin;

   function Taylor_Sin_Plus (X : Float) return Float is (X + ((X * X * X) / 6.0));

   function Taylor_Sin_Swap (X : Float) return Float is (X - ((X * X * X) / 6.0));

   function Taylor_Sin_Tight (X : Float) return Float is (X - ((X * X * X) / 6.0));

end Taylor_Sin;
