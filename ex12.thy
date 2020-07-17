theory ex12
imports
  Complex_Main
  "HOL-Library.Multiset"
begin

type_synonym rank = nat
type_synonym snat = "rank list"
abbreviation invar :: "snat \<Rightarrow> bool" where "invar s \<equiv> sorted_wrt (<) s"
definition \<alpha> :: "snat \<Rightarrow> nat" where "\<alpha> s = sum_list (map ((^) 2 ) s)"

value "\<alpha> [2, 3]"

lemmas [simp] = sorted_wrt_append
fun carry :: "rank \<Rightarrow> snat \<Rightarrow> snat" where
  "carry r [] = [r]"
| "carry r (s#ss) = (if r < s then r # s # ss else carry (r + 1) ss)"

lemma carry_invar [simp]:
  assumes "invar rs"
  shows "invar (carry r rs)"
  using assms
  apply(induction rs arbitrary: r)
   apply auto
  done

lemma [simp]: "\<alpha> [] = 0"
  by (auto simp: \<alpha>_def)

lemma [simp]: "\<alpha> (s # ss) = 2^s + \<alpha> ss"
  by (auto simp: \<alpha>_def)

lemma [simp]: "\<alpha> (ss @ ss') = \<alpha> ss + \<alpha> ss'"
  by (induction ss) (auto simp: \<alpha>_def)

lemma carry_\<alpha>:
  assumes "invar rs"
  assumes "\<forall> r' \<in>set rs. r \<le>r'"
  shows "\<alpha> (carry r rs) = 2^r + \<alpha> rs"
  using assms
  apply (induction r rs rule: carry.induct)
  by (auto simp: Suc_leI)

definition inc :: "snat \<Rightarrow> snat" where
  "inc \<equiv> carry 0"

lemma inc_invar [simp]: "invar rs \<Longrightarrow> invar (inc rs)"
  by(simp add: inc_def)

lemma inc_\<alpha>[simp]: "invar rs \<Longrightarrow> \<alpha> (inc rs) = Suc (\<alpha> rs)"
  using carry_\<alpha>
  by(simp add: inc_def)

fun add :: "snat \<Rightarrow> snat \<Rightarrow> snat" where
  "add rs1 [] = rs1"
| "add [] rs2 = rs2"
| "add (r1#rs1) (r2#rs2) = (
    if r1 < r2 then r1 # add rs1 (r2#rs2) else
    if r2 < r1 then r2 # add (r1#rs1) rs2
    else carry (r1 + 1) (add rs1 rs2)
  )"

lemma carry_lbound: "r' \<in> set (carry r'' rs) \<Longrightarrow> \<forall>x\<in>set rs. r < x \<Longrightarrow> r < r'' \<Longrightarrow>
         r < r'"
  apply(induction r'' rs rule: carry.induct)
  by (auto split: if_splits)



lemma add_lbound: "r' \<in> set (add rs1 rs2) \<Longrightarrow> \<forall>x\<in>set rs1. r < x \<Longrightarrow> \<forall>x\<in>set rs2. r < x \<Longrightarrow>
         r < r'"
  apply(induction rs1 rs2 arbitrary: r' rule: add.induct)
  by (auto split: if_splits simp: carry_lbound)
  

lemma add_invar [simp]:
assumes "invar rs1"
assumes "invar rs2"
shows "invar (add rs1 rs2)"
  using assms
  apply(induction rs1 rs2 rule: add.induct)
  using add_lbound
    apply simp_all
   apply fastforce
  done

lemma add_\<alpha>[simp]:
  assumes "invar rs1"
  assumes "invar rs2"
  shows "\<alpha> (add rs1 rs2 ) = \<alpha> rs1 + \<alpha> rs2"
  using assms
  apply(induction rs1 rs2 rule: add.induct)
  using add_lbound
  by (auto simp: Suc_leI carry_\<alpha>)

lemma size_snat:
assumes "invar rs"
shows "2^length rs \<le> \<alpha> rs + 1"
proof-
  have "2^length rs =  sum ((^) (2::nat)) {0::nat..<length rs} + 1"
    using sum_power2[where k = "length rs"]
    by auto
  also have "... \<le> \<alpha> rs + 1"
    unfolding \<alpha>_def
    by (auto simp: sorted_wrt_less_sum_mono_lowerbound[OF _ assms(1)])
  finally show ?thesis
    .
qed

fun t_carry :: "rank \<Rightarrow> snat \<Rightarrow> nat" where
  "t_carry r [] = 1"
| "t_carry r (s#ss) = (if r < s then 1 else 1 + t_carry (r + 1) ss)"

definition t_inc :: "snat \<Rightarrow> nat" where
  "t_inc = t_carry 0"

lemma t_carry_bound_aux:
  shows "t_carry r rs \<le> length rs + 1"
  apply(induction r rs rule: t_carry.induct)
  by auto

lemma t_carry_bound:
  assumes "invar rs"
  shows "t_carry r rs \<le> log 2 (\<alpha> rs + 1 ) + 1"
proof-
  have "t_carry r rs \<le> length rs + 1"
    using t_carry_bound_aux .
  also have "... \<le> log 2 (\<alpha> rs + 1) + 1"
    using le_log2_of_power[OF size_snat[OF assms]]
    by auto
  finally show ?thesis
    using of_nat_le_iff
    by simp
qed

lemma t_inc_bound:
  assumes "invar rs"
  shows "t_inc rs \<le> log 2 (\<alpha> rs + 1 ) + 1"
  using t_carry_bound[OF assms]
  by (auto simp: t_inc_def)


fun t_add :: "snat \<Rightarrow> snat \<Rightarrow> nat" where
  "t_add rs1 [] = 1"
| "t_add [] rs2 = 1"
| "t_add (r1#rs1) (r2#rs2) = (
    if r1 < r2 then 1 + t_add rs1 (r2#rs2) else
    if r2 < r1 then 1 + t_add (r1#rs1) rs2
    else 1 + (t_add rs1 rs2) + (t_carry (r1 + 1) (add rs1 rs2))
  )"

lemma t_carry_tree_length:
  "t_carry r rs + length (carry r rs) = 2 + length rs"
by (induction r rs rule: carry.induct) auto

lemma t_add_length:
  "length (add rs1 rs2) + t_add rs1 rs2 \<le> 2 * (length rs1 + length rs2) + 1"
by (induction rs1 rs2 rule: t_add.induct)
   (auto simp: t_carry_tree_length algebra_simps)

lemma t_add_bound:
fixes rs1 rs2
defines "n1 \<equiv> \<alpha> rs1"
defines "n2 \<equiv> \<alpha> rs2"
assumes INVARS : "invar rs1" "invar rs2"
shows "t_add rs1 rs2 \<le> 4 *log 2 (n1 + n2 + 1 ) + 2"
proof-
  define n where "n = n1 + n2"

  from t_add_length[of rs1 rs2]
  have "t_add rs1 rs2 \<le> 2 * (length rs1 + length rs2) + 1" by auto
  hence "(2::nat)^t_add rs1 rs2 \<le> 2^(2 * (length rs1 + length rs2) + 1)"
    by (rule power_increasing) auto
  also have "\<dots> = 2*(2^length rs1)\<^sup>2*(2^length rs2)\<^sup>2"
    by (auto simp: algebra_simps power_add power_mult)
  also note size_snat[OF INVARS(1)]
  also note INVARS(2)[THEN size_snat]
  finally have "2 ^ t_add rs1 rs2 \<le> 2 * (n1 + 1)\<^sup>2 * (n2 + 1)\<^sup>2"
    by (auto simp: power2_nat_le_eq_le n1_def n2_def)
  from le_log2_of_power[OF this] have "t_add rs1 rs2 \<le> log 2 \<dots>"
    by simp
  also have "\<dots> = log 2 2 + 2*log 2 (n1 + 1) + 2*log 2 (n2 + 1)"
    by (simp add: log_mult log_nat_power)
  also have "n2 \<le> n" by (auto simp: n_def)
  finally have "t_add rs1 rs2 \<le> log 2 2 + 2*log 2 (n1 + 1) + 2*log 2 (n + 1)"
    by auto
  also have "n1 \<le> n" by (auto simp: n_def)
  finally have "t_add rs1 rs2 \<le> log 2 2 + 4*log 2 (n + 1)"
    by auto
  also have "log 2 2 \<le> 2" by auto
  finally have "t_add rs1 rs2 \<le> 4*log 2 (n + 1) + 2" by auto
  thus ?thesis unfolding n_def by (auto simp: algebra_simps)
qed


end