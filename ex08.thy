theory ex08
imports
  Complex_Main
  "HOL-Data_Structures.Tree23_Set"
begin

term Tree23_Set.ins

fun join :: "'a tree23 \<Rightarrow> 'a tree23 \<Rightarrow> 'a upI" where
  "join Leaf Leaf = TI Leaf"
| "join (Node2 l1 a r1) (Node2 l2 b r2) = 
    (case join r1 l2 of TI t \<Rightarrow> TI (Node3 l1 a t b r2)
                      | OF t1 c t2 \<Rightarrow> OF (Node2 l1 a t1) c (Node2 t2 b r2))"
| "join (Node2 l1 a r1) (Node3 l2 b m2 c r2) = 
    (case join r1 l2 of TI t \<Rightarrow> OF (Node2 l1 a t) b (Node2 m2 c r2)
                      | OF t1 d t2 \<Rightarrow> OF (Node2 l1 a t1) d (Node3 t2 b m2 c r2))"
| "join (Node3 l1 a m1 b r1) (Node2 l2 c r2) = 
    (case join r1 l2 of TI t \<Rightarrow> OF (Node2 l1 a m1) b (Node2 t c r2)
                      | OF t1 d t2 \<Rightarrow> OF (Node3 l1 a m1 b t1) d (Node2 t2 c r2))"
| "join (Node3 l1 a m1 b r1) (Node3 l2 c m2 d r2) = 
    (case join r1 l2 of TI t \<Rightarrow> OF (Node3 l1 a m1 b t) c (Node2 m2 d r2)
                      | OF t1 e t2 \<Rightarrow> OF (Node3 l1 a m1 b t1) e (Node3 t2 c m2 d r2))"

lemma join_inorder:
fixes t1 t2 :: "'a tree23"
assumes "height t1 = height t2"
assumes "complete t1" "complete t2"
shows "inorder (treeI (join t1 t2 )) = (inorder t1 @ inorder t2)"
  using assms
  apply(induction t1 t2 rule: join.induct)
          apply (auto split: upI.splits)
  done


lemma join_complete:
fixes t1 t2 :: "'a tree23"
assumes "height t1 = height t2"
assumes "complete t1" "complete t2"
shows "complete (treeI (join t1 t2 )) \<and> height (join t1 t2 ) = height t2"
  using assms
  apply(induction t1 t2 rule: join.induct)
          apply (auto split: upI.splits)
  done


find_theorems "size" "complete"
find_theorems "_ ^ _" "log"

lemma height_bound_upper: "complete t \<Longrightarrow> height t \<le> log 2 (size t + 1 )"
  using ht_sz_if_complete  le_log2_of_power
  by blast

lemma height_bound_lower_aux: "complete t \<Longrightarrow> size t + 1 \<le> 3 ^ height t"
  apply(induction t)
    apply auto
  done

find_theorems "log" "log _ _ \<le> _"

lemma height_bound_lower:
  assumes "complete t"
  shows "log 3 (size t + 1 ) \<le> height t"
proof-
  have "real (size t + 1) \<le> 3 ^ height t"
    using height_bound_lower_aux[OF assms]
    using of_nat_mono
    by fastforce
  hence "log 3 (size t + 1) \<le> log 3 (3 ^ height t)"
    using log_le_cancel_iff[where a = 3 and x = "(size t + 1)" and y = "3 ^ height t", symmetric]
    by auto
  moreover have "log 3 (3 ^ height t) = height t"
    using log_pow_cancel
    by force
  ultimately show ?thesis
    by auto
qed
