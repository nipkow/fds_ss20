theory ex14_tut
  imports "HOL-Library.Multiset"
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.RBT"
  "HOL-Library.Char_ord"
begin

definition freq :: " 'a list \<Rightarrow> 'a \<Rightarrow> nat"
  where "freq ws = count (mset ws)"

value "count (mset [''a'', ''b'', ''a'']) ''b''"

definition is_freq_list :: "'a list \<Rightarrow> ('a \<times> nat) list \<Rightarrow> bool" where
  "is_freq_list ws fl = (sorted (rev (map snd fl))
                         \<and> distinct (map fst fl)
                         \<and> (\<forall>(w,f)\<in>set fl. f = freq ws w))"

  lemma \<open>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''c'',2),(''b'',2),(''a'',1)]\<close>
  (*<*)
    unfolding is_freq_list_def freq_def by auto
  (*>*)
  lemma \<open>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',2),(''a'',1)]\<close>
  (*<*)
    unfolding is_freq_list_def freq_def by auto
  (*>*)
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',3),(''a'',1)]\<close>
  (*<*)
    unfolding is_freq_list_def freq_def by auto
  (*>*)
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''a'',1),(''c'',2),(''b'',2)]\<close>
  (*<*)
    unfolding is_freq_list_def freq_def by auto
  (*>*)
  lemma \<open>\<not>is_freq_list [''a'',''b'',''b'',''c'',''c''] [(''b'',2),(''c'',2),(''b'',2),(''a'',1)]\<close>
  (*<*)
    unfolding is_freq_list_def freq_def by auto
  (*>*)

definition incr1 :: "'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> nat" where
  "incr1 x f = f(x := Suc (f x))"

definition "freq1 ws \<equiv> fold incr1 ws (\<lambda>_. 0 )"

value "(freq1 [''a'',''b'',''b'',''c'',''c'']) ''c''"

lemma freq1_correct: "freq1 ws = freq ws"
proof - 
  
  have "fold incr1 ws f w = count (mset ws) w + f w" for w f
  apply(induction ws arbitrary: f)
    by (auto simp: incr1_def)
  then show ?thesis
    by (auto simp: freq1_def freq_def)
qed

  definition abs_fm :: "('a::linorder,nat) rbt \<Rightarrow> 'a \<Rightarrow> nat" where
    "abs_fm t k \<equiv> case RBT.lookup t k of None \<Rightarrow> 0 | Some v \<Rightarrow> v"

  definition inv_fm :: "('a::linorder,nat) rbt \<Rightarrow> bool" where
    "inv_fm t \<equiv> (0 \<notin> ran (RBT.lookup t))"
                       
  lemma empty2_correct[simp]:
    "abs_fm RBT.empty = (\<lambda>_. 0)" "inv_fm RBT.empty"
    by(auto simp add: abs_fm_def inv_fm_def)

term RBT.insert

definition incr2 :: "'a::linorder \<Rightarrow> ('a, nat) rbt \<Rightarrow> ('a, nat) rbt" where
  "incr2 x t = RBT.insert x (Suc (abs_fm t x)) t"

lemma incr2_correct[simp]:
"inv_fm t \<Longrightarrow> abs_fm (incr2 k t) = incr1 k (abs_fm t)"
"inv_fm t \<Longrightarrow> inv_fm (incr2 k t)"
  by (auto simp add: ran_def inv_fm_def incr1_def abs_fm_def incr2_def split: option.splits)

(*"inv_fm t \<Longrightarrow> inv_fm (incr2 k t)"*)

definition "freq2 ws \<equiv> fold incr2 ws RBT.empty"


lemma "inv_fm t \<Longrightarrow> (abs_fm (fold incr2 ws t) = fold incr1 ws (abs_fm t)) \<and> inv_fm (fold incr2 ws t)"
  apply(induction ws arbitrary: t)
  by auto

lemma freq2_correct: "abs_fm (freq2 ws) = freq1 ws" (is ?g1) "inv_fm (freq2 ws)" (is ?g2)
proof - 
  have "inv_fm t \<Longrightarrow> (abs_fm (fold incr2 ws t) = fold incr1 ws (abs_fm t)) \<and> inv_fm (fold incr2 ws t)" for t
    apply(induction ws arbitrary: t)
    by auto
  thus ?g1 ?g2
    by(auto simp add: freq2_def freq1_def)
qed

find_theorems "_:: ('a , 'b)  rbt \<Rightarrow> ('a \<times> 'b) list"

definition fsort :: "'a::linorder list \<Rightarrow> ('a \<times> nat) list" where
  "fsort ws = rev (sort_key snd (RBT.entries (freq2 ws)))"

value "fsort [1::nat, 2, 2, 3, 3]"

lemma Some_iff: "RBT.lookup (freq2 ws) w = Some f \<longleftrightarrow> (freq ws w = f \<and> f > 0)"
proof-
  have "RBT.lookup (freq2 ws) w = Some f \<longleftrightarrow> abs_fm (freq2 ws) w = f \<and> f > 0"
    using freq2_correct[unfolded inv_fm_def]
    apply (auto simp: abs_fm_def split: option.splits)
    by (smt \<open>\<And>ws. 0 \<notin> ran (RBT.lookup (freq2 ws))\<close> gr0I ranI)
  thus ?thesis
    by (simp add: freq1_correct freq2_correct(1))
qed

lemma lem3: "(\<forall>(w,f)\<in>set (fsort ws). f = freq ws w)"
  using Some_iff
  unfolding fsort_def
  by (metis (mono_tags, lifting) case_prodI2 lookup_in_tree set_rev set_sort)


lemma lem1: "sorted (rev (map snd (fsort ws)))"
  unfolding fsort_def
  by (simp add: rev_map)

lemma lem2: "distinct (map fst (fsort ws))"
  unfolding fsort_def
  by (metis RBT.distinct_entries distinct_map distinct_rev distinct_sort set_rev set_sort)

lemma fsort_correct: "is_freq_list ws (fsort ws)"
  unfolding is_freq_list_def
  using lem1 lem2 lem3
  by blast

definition fsort_string :: "String.literal list \<Rightarrow> (String.literal \<times> nat) list"
  where "fsort_string \<equiv> fsort"

value "fsort_string [STR ''a'', STR ''b'', STR ''b'', STR ''c'', STR  ''c'']"

export_code fsort_string in SML module_name Fsort file "export.sml"

SML_file "export.sml"

ML_val \<open>
fun file_to_string name = let
      val f = TextIO.openIn name
      val s = TextIO.inputAll f
      val _ = TextIO.closeIn f
    in s end

val f1 = "/home/ladmin/Teaching/FDS/fds/SS20//Exercises//ex14/MASC-3.0.0/data/written/non-fiction/CUP2.txt"

val it = (@{code fsort_string}) (String.tokens (not o Char.isAlpha) ((file_to_string f1)))



\<close>

end
