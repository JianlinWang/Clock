theory Clock imports Complex_Main 
(*  "~~/src/HOL/Library/Extended_Real"*) 

begin
 
type_synonym clock = "nat \<Rightarrow> real"


definition head :: "clock \<Rightarrow> real" 
      where 
   "head c \<equiv> c (0::nat)"


definition suffix :: "clock \<Rightarrow> nat \<Rightarrow> clock"  
             (infixl "|." 60)  where
   "c |. i \<equiv> \<lambda> n. c (n+i)"



definition tail :: "clock \<Rightarrow> clock"
    where
  "tail c \<equiv> \<lambda> n. c (n+1)"


definition app :: "real \<Rightarrow> clock \<Rightarrow> clock"
    (infixl "##" 60)  where
  "t ## c \<equiv> \<lambda> n. if n=0  then t  else c (n-(1::nat))"

definition isClock::"clock \<Rightarrow> bool"
   where
  "isClock c \<equiv> \<forall>i.  (c (i)) > 0 \<and> (c (i+1)) - (c i) > 0 "




definition low_rate::"clock \<Rightarrow> real"
    ("\<triangle> (_)" 60)   where 
 "low_rate c \<equiv> Inf {a. \<exists>i. a = (c (i+1)) - (c i)}"

definition high_rate::"clock \<Rightarrow> real"
    ("\<dtriangle>" 60) where
 "high_rate c \<equiv> Sup{a. \<exists>i. a=(c (i+1))- (c i)}"

definition healthy_clock::"clock \<Rightarrow> bool"
   where
  "healthy_clock c \<equiv> isClock c \<and> \<triangle>(c) > 0"


locale partial_order =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow>bool" (infixl "\<sqsubseteq>" 50)
  assumes refl:"x \<sqsubseteq> x"
  and  antisym:"\<lbrakk> x \<sqsubseteq> y ; y \<sqsubseteq> x \<rbrakk>\<Longrightarrow> x = y "
  and  trans: "\<lbrakk>x \<sqsubseteq> y; y\<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"


text{*
  Clock c is finer than clock d if d is subsequence of c,
  c \<sqsupseteq> d \<equiv> Set(d) \<subseteq> Set(c)
*}

definition  finer:: "clock \<Rightarrow> clock \<Rightarrow> bool"
     (infixl "\<sqsupseteq>" 60)  where
  "finer c d \<equiv> (isClock c) \<and> (isClock d) \<and> { x. \<exists>i. x= (c i) }  \<subseteq> {x. \<exists>i. x= (d i)} "


definition  faster::"clock\<Rightarrow>clock\<Rightarrow>bool"
    (infixl "\<lesssim>" 60 ) where
"faster c d  \<equiv> \<forall>i. (c i) \<le> (d i)"

definition clock_dis::"clock\<Rightarrow>clock\<Rightarrow>real"
   ("\<rho> _ _" 60) where
"clock_dis c d \<equiv> Sup {a. \<exists>i. a= abs((c i) - (d i)) \<and> i > 0}"



lemma suffix_first: "head (c |. n) = c n"
  by (auto simp add: suffix_def head_def)


lemma suffix_plus: "c |. n |. m = c |. (m + n)"  
apply (simp add: suffix_def nat_add_assoc)
done

lemma suffix_commute: "((c |. n) |. m) = ((c |. m) |. n)" 
apply (simp add: suffix_plus nat_add_commute)
done

lemma suffix_plus_com: 
 "c |. m |. n = c |. (m + n)"
apply (subst suffix_plus)
apply (simp add:suffix_plus nat_add_commute)
done 

lemma suffix_zero: 
 "c |. 0 = c" 
by (simp add: suffix_def)


lemma suffix_tail:
 "c |. 1 = tail c"  
by (simp add: tail_def suffix_def)

lemma tail_suffix_suc: 
  "c |. (Suc n) = tail (c |. n)" 
apply (simp add: suffix_def tail_def)
done

lemma seq_app_second: "(t ## c) 1 = c 0 "
by (simp add: app_def)


lemma seq_app_first: "(t ## c) 0 = t"  
 by (simp add: app_def)


lemma seq_app_first_tail: "(head c) ## (tail c) = c"
by (auto simp: app_def head_def tail_def) 


lemma low_rate_le_n:
assumes a1:"isClock c"
shows "\<triangle>(c)\<le> (c (n+1)) - (c n)"
proof-
  from a1 have s1:"\<forall>i. 0 < (c (i+1))- (c i)" 
       apply (simp add:isClock_def) done
  from s1 have s2:"\<forall>i. 0 \<le> (c (i+1))- (c i)"
       apply (simp add:order_less_imp_le) done
  let ?A="{a. \<exists>i. a = c (Suc i) - c i}"
    and ?x="c (Suc n) - c n"
  have s3:"?x\<in>?A" thm Inf_lower apply auto done
  from s2 have s4:"\<And>y. y\<in>?A \<Longrightarrow> 0 \<le> y"  apply auto done
  from s3 s4 have s5:"Inf ?A \<le> ?x" apply (rule Inf_lower) apply blast done
  thus  ?thesis by(simp add: low_rate_def) 
qed

lemma low_rate_le_each:
"\<lbrakk> isClock c \<rbrakk> \<Longrightarrow> \<forall>n. \<triangle>(c)\<le> (c (n+(1::nat))) - (c n)"
apply (insert low_rate_le_n)
apply auto
done

lemma low_rate_le_sum:
assumes a1:"isClock c "
shows "((real (Suc n))*(\<triangle> c))\<le> (\<Sum>i = 0..n. ((c (Suc i)) - (c i)))"
proof(induct n)
  case 0
    let ?X0 = "(\<Sum>i = 0..0. ((c (Suc i)) - (c i)))"
    have s1:"((real (Suc 0))*(\<triangle> c))= (\<triangle> c)" by simp
    have s2: "?X0= ((c (Suc 0)) - (c 0))"  by simp
    from a1 have s4:"(\<triangle> c) \<le> ((c (Suc 0)) - (c 0))" 
       using  low_rate_le_each  by auto
    from s1 s4 show ?case by simp
next
   case (Suc n)
   let ?Xn="(\<Sum>i=0..n. ((c (Suc i)) - (c i)))"
     and ?Yn="(\<Sum>i = 0..(Suc n). (c (Suc i)) - (c i))"
   have s5: "?Yn = ?Xn + (c (Suc (Suc n))) - (c (Suc n))" 
    apply simp  done 
   from a1 have s7 : "(\<triangle> c)\<le> (c (Suc (Suc n))) - (c (Suc n))"
      using  low_rate_le_each  apply simp done
   have s8:"(real (Suc n)) * (\<triangle> c) \<le>  ?Xn" apply (rule Suc.hyps) done 
   from s5 s7 s8 have s9:"(real (Suc n)) * (\<triangle> c) + (\<triangle> c) \<le> ?Yn" 
      apply simp done  
   have s10:"(real (Suc (Suc n)))*(\<triangle> c) = ((real (Suc n)) + (1::real))*(\<triangle> c)"
      apply simp done
   have s11:"((real (Suc n)) + (1::real)) * (\<triangle> c) = (real (Suc n)) * (\<triangle> c) + (\<triangle> c)"
      apply (auto simp: mult_Real add_Real algebra_simps) done
   from s10 s11 have  s12: "(real (Suc (Suc n))) * (\<triangle> c)= (real (Suc n)) * (\<triangle> c) + (\<triangle> c)"
      apply simp done
   from s8 s9 s12 show ?case apply simp  done 
qed



lemma clock_le:
  assumes a0:"isClock c"
  and    a1:"i< j"
  shows "(c i) < (c j)"
proof-
  from a0 have s1: "\<And>i. 0 < (c (Suc i) - (c i))" apply (simp add:isClock_def) done
   from s1 have s2:"\<And>i. (c i) < c (Suc i)" 
             
             apply m  done


thm lift_Suc_mono_less
lemma clock_le_order:
  "\<lbrakk>isClock c; i<j \<rbrakk> \<Longrightarrow> (c i) < (c j)"
apply (unfold isClock_def)
apply (rule_tac f=c and n=i and n'=j in lift_Suc_mono_less)
apply (subgoal_tac "0< c (Suc n) - (c n)")
apply (rotate_tac 2)
apply 
proof(induct i)
case 0
   have "(\<Sum>n = 0..(j - (1::nat)). c (Suc n) - c n) = c j - c 0" 
     proof(induct "j-(1::nat)")
     case 0
       have s1:"0 =j-(1::nat)"  apply (rule Suc.hyps) done
       have s2:"0 = j - 1 \<Longrightarrow> (\<Sum>n = 0..j - 1. c (Suc n) - c n) = c j - c 0"
         proof-
            assume aa1:"(0::nat)= j - (1::nat)"
            show  ss1: "(\<Sum>n = 0..(j - (1::nat)). c (Suc n) - c n) = c j - c 0"
            proof-
               from a1 aa1 have ss2:"j= Suc 0" apply simp    done   
               from ss2 have ss3:"(\<Sum>n = (0::nat)..(0::nat). ((c (Suc 0)) - (c (0::nat)))) 
                                  = ((c (Suc 0)) - (c (0::nat)))" apply auto done
             from ss3 ss2 show ?thesis apply auto done
             qed
         qed
         thus  ?case  apply simp apply auto 
      next 
       case Suc 
       have 
  
case (Suc i) 
  "\<lbrakk> \<forall>(k::nat). (c k)< c (Suc k); i<j\<rbrakk>\<Longrightarrow> c i < c j"
apply(induct i)
apply b
apply (simp add:isClock_def)
apply ()
apply auto
done


lemma healthy_clock_0: 
 assumes a1:"isClock c"
 shows "(\<Sum>i=0..n. ((c (Suc i)) - (c i))) = ((c (Suc n)) - (c (0::nat)))"
proof (induct n)
case 0
  have "(\<Sum>i = 0..0. ((c (Suc i)) - (c i))) = ((c (Suc (0::nat))) - (c (0::nat)))"
     by auto
  thus  ?case .  
next
  case (Suc n)
  let ?X = "\<Sum>i = 0..(Suc n). ((c (Suc i)) - (c i)) "
   and ?Y = "\<Sum>i = 0..n. (c (Suc i) - (c i))"
  have s1: "?X = ?Y + (c (Suc (Suc n))) - (c (Suc n))"  
    apply simp done
  also have s2:"?Y = (c (Suc n)) - (c (0::nat))"
     apply (rule Suc.hyps) done
  from s1 s2 have s3: "?Y + ((c (Suc (Suc n))) - (c (Suc n))) =
            ((c (Suc n)) - (c (0::nat)))
           +((c (Suc (Suc n))) - (c (Suc n)))"
  apply (auto simp:s1 s2)  done
  from s3 have s4: "?Y
           + ((c (Suc (Suc n))) - (c (Suc n))) 
        = (c (Suc (Suc n))) - (c (0::nat))"
   by auto
  from s1 s4 have s5:"?X = (c (Suc (Suc n))) - (c (0::nat))" by auto
  from s5 show ?case by auto
qed

lemma healthy_clock_1:
  "isClock c \<Longrightarrow>((real (Suc n))*(\<triangle> c))  \<le> c (Suc n) -  (c 0)"
  apply (insert low_rate_le_sum)
  apply (insert healthy_clock_0)
  apply simp
done

lemma healthy_clock_2:
  "isClock c \<Longrightarrow> ( (real (n::nat)) * (\<triangle> c) \<le> ((c n) - (c 0)))" 
apply(induct n)
apply simp
apply (simp add:healthy_clock_1)  
done

lemma real_le_0: "\<lbrakk>a \<le> b - c; (0::real) < c\<rbrakk> \<Longrightarrow> a <b"
apply simp
done

lemma healthy_clock_3:
 "isClock c \<Longrightarrow> ( (real (n::nat)) * (\<triangle> c) < ((c n))) "
apply(rule_tac c="(c 0)" in real_le_0)
apply(simp add: healthy_clock_2)
apply(simp add:isClock_def)
done


lemma  real_mult_le: "\<lbrakk> a \<le> b ; 0 < d \<rbrakk> \<Longrightarrow> a*d \<le> b*(d::real)"
apply simp 
done

lemma real_mult_add:"(a + 1)*b = a*b + (b::real)"
apply (auto simp: mult_Real add_Real algebra_simps)
done

lemma non_zeno_behaviour:"healthy_clock c \<Longrightarrow> \<forall>E. \<exists>N. E < (c N)"
proof
 fix E assume a0:"healthy_clock c"
  show  "\<exists>N. E < (c N)"
proof-
 from a0 have s1:"isClock c"  by (simp add:healthy_clock_def) 
 from a0 have s2:"0 < \<triangle>(c)" by (simp add:healthy_clock_def) 
   let ?M="(E/(\<triangle> c))"
   from s1 s2 have s3: "E = (?M*(\<triangle> c))" by auto
   have s4:"?M \<le> (natceiling ?M)" 
    using real_natceiling_ge[of "?M"] apply blast  done
   from s2 s4 have s5:"(?M*(\<triangle> c)) \<le> (natceiling ?M)*(\<triangle> c)"       
     using  real_mult_le[of "?M" "(natceiling ?M)" "(\<triangle> c)"]
     apply simp done
   from s3 s5 have s6:"E \<le> (natceiling ?M)*(\<triangle> c) " by simp
   from s2 s6 have s7: "E < (natceiling ?M)*(\<triangle> c) + (\<triangle> c)"
      apply auto done
   from s2 have s8: "(natceiling ?M)*(\<triangle> c) + (\<triangle> c) =((natceiling ?M)+(1::real))*(\<triangle> c)"   
      apply(auto simp: mult_Real add_Real algebra_simps)  done
   from s2 have s9:"((natceiling ?M)+(1::real))*(\<triangle> c) =
                    (Suc(natceiling ?M))*(\<triangle> c)"
      apply auto done
   from s8 s9 have s10: "(natceiling ?M)*(\<triangle> c) + (\<triangle> c) = (Suc(natceiling ?M))*(\<triangle> c)"
      apply simp done
   from s1 have  s11:" (Suc(natceiling ?M))*(\<triangle> c) < (c (Suc(natceiling ?M)))"
      using  healthy_clock_3[of "c" "(Suc(natceiling ?M))"] 
        apply auto done
   from s11 have s12:"\<lbrakk> E < (Suc(natceiling ?M))*(\<triangle> c)\<rbrakk> \<Longrightarrow> \<exists>(N::nat). E < (c N)" 
      apply(rule_tac x=" (Suc(natceiling ?M))" in exI) 
      apply (simp) done
   from s7 s10 s12 
    show ?thesis apply auto  done 
  qed
qed




subsection{*Paritial order on clocks*}




lemma finer_refl:"isClock c \<Longrightarrow>finer c c"
apply (simp add:finer_def)
done



lemma "\<lbrakk>c \<sqsupseteq> d; d \<sqsupseteq> c \<rbrakk> \<Longrightarrow> \<forall>i. \<exists>j. d i = c j"
apply (simp add:finer_def) 
apply blast
done

lemma "\<lbrakk>c \<sqsupseteq> d; d \<sqsupseteq> c \<rbrakk> \<Longrightarrow> \<forall>i. \<exists>j. c i = d j"
apply (simp add:finer_def) 
apply blast
done
lemma finer_antisym_0:
  assumes a0:"c \<sqsupseteq> d"
   and    a1:"d \<sqsupseteq> c "
  shows   "(d 0) < (c 0) \<Longrightarrow> False"
proof-
  assume a2:"(d 0) < (c 0)"
  show "False"
  proof-
  from a0 a1 have s1: "\<exists>i. d 0 = c i" 
     apply (simp add:finer_def)
     apply blast done
  from a2 s1 have s2 : "\<exists>i. (c i) < (c 0)"  apply auto done
  from a0 a1 have "" 
qed
lemma finer_antisym_0:
  assumes a0:"c \<sqsupseteq> d"
   and    a1:"d \<sqsupseteq> c "
  shows   "d 0 = c 0"
proof-
   have  a3: "d 0 \<noteq> c 0 \<Longrightarrow> False"
   proof-
      assume a4:"d 0 \<noteq> c 0"
      show "False"  
      proof-
        assume a5:"(d 0) < (c 0)"
        assume a6:"(c 0)< (d 0)"


lemma finer_antisym:"\<lbrakk>isClock c ; isClock d;finer c d ; finer d c\<rbrakk> \<Longrightarrow> c = d "
apply(simp add:finer_def isClock_def)
apply blast
apply 
text{*
  \<sqsupseteq> is a partial order on the set of clocks.
*}

thm

(*
lemma 
*)

subsection{*Least upper bound*}
text{*
  Let c and d be clocks. We define c \<parallel> d as the least upper bound of c and d
with respect the partial order \<sqsupseteq>:
*}
(*lub \<equiv>  Least upper bound*)



(*function lub :: "clock\<Rightarrow>clock\<Rightarrow>clock"
   where
"lub c d =(if (head c) = (head d) then (head c)##(lub (tail c) (tail d)) 
           else (if (head c)>(head d) then (head d)##(lub c (tail d))
                 else (head c)##(lub (tail c) d)))"
apply auto
 *)


fun lub_c lub_d :: "clock \<Rightarrow> clock \<Rightarrow>nat \<Rightarrow> nat"
   where  
"lub_c c d zero = zero"|
"lub_d c d zero = zero"|
"lub_c c d n =(if  (c ((lub_c c d (n-one))+one)) = (d ((lub_d c d (n-one))+one)) then  (lub_c c d (n-one))+one 
               else (if (c ((lub_c c d (n-one))+ one)) > (d ((lub_d c d (n-one))+one)) then (lub_c c d (n-one)) 
                     else (lub_c c d (n-one))+one ))"|

"lub_d c d n =(if (c ((lub_c c d (n-one))+one)) = (d ((lub_d c d (n-one))+one)) then  (lub_d c d (n-one))+one 
               else (if (c ((lub_c c d (n-one))+one)) > (d ((lub_d c d (n-one))+one)) then (lub_d c d (n-one))+one 
                     else (lub_d c d (n-one))))"

lemma  lub_c_d_zero_eq:"lub_c c c zero = lub_d c c zero"
by auto

lemma lub_c_zero_eq:"lub_c c c zero = zero"
by auto
lemma lub_d_zero_eq : "lub_d c c zero = zero"
by auto

lemma lub_c_n_eq:"lub_c c c n = n"
apply(induct_tac n)
apply (simp add: lub_c_zero_eq)
sorry
(*
apply (auto simp:lub_d_def lub_c_def lub_c_lub_d_sumC_def lub_c_lub_d_graph_def Inl_def )

lemma lub_c_d_n_eq:"lub_c c c n = lub_d c c n"
apply (induct_tac n)
by auto

definition lub ::"clock\<Rightarrow> clock\<Rightarrow>clock"
   (infixl "\<parallel>" 60) where
"lub c d \<equiv> \<lambda>n. (if (c (lub_c c d n)) = (d (lub_d c d n)) then (c (lub_c c d n)) 
                 else (if (c (lub_c c d n)) > (d (lub_d c d n)) then (d (lub_d c d n)) 
                       else (c (lub_c c d n))  ))"

lemma lub_eq: 
  assumes a0:"(c \<parallel> c) n = c n"
  shows "(c \<parallel> c) (Suc n) = c (Suc n)"
proof-
 from a0 have s1:"luc_c c c n = c n"  
           apply (auto simp:lub_def)
           apply (auto simp:lub_c_d_n_eq )
lemma " (c \<parallel> c) n  = c n"
apply (induct_tac n)
apply (simp add:lub_c_d_zero_eq lub_def)
apply(unfold lub_def)
apply (insert )
apply (auto simp:lub_c_d_n_eq lub_def)
apply auto
lemma *)
  (*

function
  lub:: "clock \<Rightarrow> clock \<Rightarrow> clock"
      (infixl "\<parallel>" 60) where  
"lub (c::clock) (d::clock)  = ( if (c 1) = (d 1) then  (c 1)##(lub (tail c) (tail d))   
              else  ( if (c 1) > (d 1) then (d 1)##(lub c (tail d))
                else (c 1)##( lub (tail c) d) ))"  
by  auto*)

(*termination *)
(*declare lub.simps[simp del]*)
(*apply simp
print_theorems*)
(* lub.cases lub.pinduct lub.psimps *)
(*
lemma "c\<parallel>c = c"
apply (unfold lub_def)
apply (unfold lub_sumC_def)
apply (unfold lub_graph_def)
thm nat.induct

apply auto
primrec
definition mft:: "clock\<Rightarrow>clock\<Rightarrow>real"
  where 
"mft c d \<equiv> if (c 1) > (d 1) then (d 1) else (c 1)"



fun lub:: "clock \<Rightarrow> clock \<Rightarrow> clock"
    where 
" lub c  d = (mft c d) ##(lub (tail c)  (tail d))"  
inductive
*)

lemma " (lub c  d)= lub d  c"
sorry
 
lemma "(lub c (lub d e)) = (lub (lub c d) e)"
sorry

lemma " c \<subseteq> (lub c d )"
sorry

lemma "\<lbrakk> c \<subseteq> e; d \<subseteq> e  \<rbrakk> \<Longrightarrow> (lub c d) \<subseteq> e"
sorry

lemma " d \<subseteq> c \<Longrightarrow> ( c = (lub c d))"
sorry

lemma "( c = (lub c d)) \<Longrightarrow>d \<subseteq> c  "
sorry

text{*
   Partial Order Again.
c is clock, c runs faster than d if for all i \<ge> 1, 
having  c[i]\<le> d[i].
We denote this relation by c \<lesssim> d. 
*}



text{*
  Lemma : faster is a partial order on clocks.  
  *}
(*
  lemma  faster is a partial order on clocks.
  *)

lemma less_le_real :"(0::real) < (b::real) -a \<Longrightarrow> a \<le> b"
apply arith
done

lemma "\<lbrakk> isClock c\<rbrakk> \<Longrightarrow> c \<lesssim> (tail c)"
apply (auto simp:isClock_def faster_def tail_def)
apply (simp add:less_le_real)
done
     
lemma "\<lbrakk>isClock c1; isClock c2; isClock d; c1 \<lesssim> c2 \<rbrakk>
    \<Longrightarrow> (lub c1 d) \<lesssim> (lub c2 d) "
sorry

text{*
  Metric Space of Clocks.
Let c and d be clocks.
Define
p (c, d) = sup{abs(c[i] - d[i]) | i \<ge> 1}
*}


lemma "\<rho> c d \<ge> (0 ::real)"
sorry

lemma "\<rho> c d = 0 \<Longrightarrow> c  = d"
sorry

lemma "c = d \<Longrightarrow> \<rho> c d = 0"
sorry

lemma "\<rho> c d  = \<rho> d c"
sorry

lemma "\<rho> c e \<le> (\<rho> c d) + (\<rho> d e)"
sorry

text{*
Example:
  Let in and out be clocks recording time instants when
input and output of a buffer occur respectively.
Because the output is always preceded by the corresponding input,
the buffer meets the following requirement.
in \<lesssim> out
It transmission latecy can be specified by \<rho>(in ,out).
One cell buffer can be specified by 
in \<lesssim> out \<lesssim> in'  (tail in)
  *}

text{*
Clock Operations
    *}



text{*
Clock Operations::Projection
Let c be a clock, and P(i):Nat \<longrightarrow> bool a predicate.
The notation P \<lhd> c denotes the clock define by:
(P \<lhd> c  \<equiv>  if P(1)
            then c[1] ## (P(i+1) \<lhd> c')
            else P(i+1) ##  

)
    *}

type_synonym projection_predicate = "nat \<Rightarrow> bool"
(*
fun  projectI ::"projection_predicate\<Rightarrow> clock\<Rightarrow>real"
   where
"projectI P c = (if (P (0::nat)) then (head c) 
                  else ( projectI (\<lambda>n.(P (n+(1::nat)))) (tail c) ))"
*)
(*
inductive_set clock_project::"nat\<Rightarrow>bool \<Rightarrow> clock"
pro_zero:"\<lambda>n. (if (P n) )"
*)
(*
definition P ::"nat\<Rightarrow>bool"
where
"P i \<equiv> "
*)

text{*
Clock Operations
Filter
    *}

text{*
Clock Operations
Shift
Let r be a real number.
The notation r \<guillemotright> c represents the clock defined by
r\<guillemotright> c  = c[0]+r ## (r \<guillemotright> c')
    *}
definition clock_shift::"real\<Rightarrow>clock\<Rightarrow>clock"
  (infixl "\<guillemotright>" 60) where
"clock_shift r c \<equiv> \<lambda>n. ((c n)+ r)"

lemma "0\<guillemotright>c=c"
apply (simp add:clock_shift_def)
done

lemma "r1\<guillemotright>(r2\<guillemotright>c) = (r1+r2)\<guillemotright>c"
apply (simp add:clock_shift_def)
apply auto
done

lemma "c \<lesssim> d \<Longrightarrow> (r\<guillemotright>c) \<lesssim> (r\<guillemotright>d)"
apply (simp add:clock_shift_def faster_def)
done

text{*
Event vs Clock
Let e be an event.
We will use the notation clock(e) to denote the clock 
that records the time instants when the event e occurs.
Let c be a clock.
We will use the notation event(c) to denote the event that
take place at every time instant c[i].
clock(event(c) = c) 
    *}

text{*
Local Clock
Let l be a label denoting a logical location, 
and c a clock.
The notation  l |:c 
represents the clock c that resides at l.
We extend the definitions of 
    *}

text{*
Time Difference.
For location l and m, 
We use   \<delta> t (l m)
to represent the time difference between l and m.
\<delta> t is subject to the following laws:
Law 1 \<delta> t (l m) = - \<delta> t (m l)
Law 2 \<delta> t (l m) = \<delta> t (l m)    
    *}

datatype location ="location"


locale location =
 fixes time_diff ::"location \<Rightarrow>location \<Rightarrow>real"
 assumes td1 :"time_diff m l = -(time_diff l m)"
     and td2 :"time_diff m l = (time_diff m h)+(time_diff h l)"
	 
lemma real_zero:"(a::real) = -a \<Longrightarrow> a=(0::real)"
apply arith
done
lemma (in location) td1_1:"time_diff m m = -(time_diff m m)"
apply (insert td1)
apply blast
done

lemma (in location)"time_diff m m = (0::real)"
apply (insert td1)
apply (insert td1_1)
apply (insert real_zero)
apply blast
done
text{*
  Counterpart
Let l:c be a clock, and m be a location.
The notation m:(l:c) stand for the counterpart of the local clock
l:c at the location m
 m:(l:c) = m:((time_diff l m)\<guillemotright>c)
  *}
(*
lemma "l:(l:c) = l:c"
lemma "l:(m:(l:c))=l:c"
lemma "l1:(l2:(l3:c))=l1:(l3:c)"
*)
thm inv_def
thm Hilbert_Choice.someI
thm Hilbert_Choice.someI2
lemma choice_lemma: "\<lbrakk>P a;\<And>x. P x \<Longrightarrow> Q x \<rbrakk>\<Longrightarrow> Q a"
apply simp
done
lemma nat_indut:"\<lbrakk> (\<And>i. (P (i::nat)) \<Longrightarrow> (Q i)); P (n::nat) \<rbrakk>\<Longrightarrow> Q n"
apply (simp)
done
lemma "\<And>i. \<lbrakk>f (0::nat) = (d 0::nat); 
        \<And>n. (f n::nat) = d n \<Longrightarrow> f (Suc n)= d (Suc n)\<rbrakk>\<Longrightarrow>
       f i = d i"
apply (induct_tac i)
apply blast
apply (erule_tac P="\<lambda>j. (f j = d j)" and Q="\<lambda>j.(f (Suc j)) = d (Suc j)" 
  in nat_indut)
apply assumption
done


end

