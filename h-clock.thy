theory H-Clock imports Clock begin
lem

{*
Paritial order on clocks
  Clock c is finer than clock d if d is subsequence of c,

*}
definition  finer:: "clock \<Rightarrow> clock \<Rightarrow> bool"
     (infixl "" 60)  where
  "finer c d \<equiv> "   

end