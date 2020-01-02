theory Healty_Clock imports Clock begin

definition
  "lower_bound A = {a . \<forall> x \<in> A . a \<le> x}"

definition
  "infimum A = {a \<in> lower_bound A . (\<forall> x \<in> lower_bound A . x \<le> a)}"

definition
  "upper_bound A = {a . \<forall> x \<in> A . x \<le> a}"

definition
  "supremum A = {a \<in> upper_bound A . (\<forall> x \<in> upper_bound A . a \<le> x)}"



end 