theory Auto_Proof_Demo
imports Main
begin

section "Logic and sets"

lemma "ALL x. EX y. x=y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text \<open>Note the bounded quantification notation:\<close>

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce


text \<open>Most simple proofs in FOL and set theory are automatic.
Example: if T is total, A is antisymmetric and T is a subset of A, then A is a subset of T.\<close>

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast


section "Sledgehammer"

lemma "R^* \<subseteq> (R \<union> S)^*"
oops

text \<open>Find a suitable P and try sledgehammer:\<close>

lemma "a # xs = ys @ [a] \<Longrightarrow> P"
oops


section "Arithmetic"

lemma "\<lbrakk> (a::int) \<le> f x + b; 2 * f x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
by arith

lemma "\<forall> (k::nat) \<ge> 8. \<exists> i j. k = 3*i + 5*j"
by arith

lemma "(n::int) mod 2 = 1 \<Longrightarrow> (n+n) mod 2 = 0"
by arith

lemma "(i + j) * (i - j) \<le> i*i + j*(j::int)"
by (simp add: algebra_simps)

lemma "(5::int) ^ 2 = 20+5"
by simp

end
