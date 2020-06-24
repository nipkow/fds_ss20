theory ex09_2
  imports Main "HOL-Data_Structures.RBT_Set"
begin

fun ins' :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt option" where
"ins' x Leaf = Some (R Leaf x Leaf)" |
"ins' x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> (case (ins' x l) of None \<Rightarrow> None | Some t \<Rightarrow> Some (baliL t a r)) |
     GT \<Rightarrow> (case (ins' x r) of None \<Rightarrow> None | Some t \<Rightarrow> Some (baliR l a t)) |
     EQ \<Rightarrow> None)" |
"ins' x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> (case (ins' x l) of None \<Rightarrow> None | Some t \<Rightarrow> Some(R t a r)) |
    GT \<Rightarrow> (case (ins' x r) of None \<Rightarrow> None | Some t \<Rightarrow> Some (R l a t)) |
    EQ \<Rightarrow> None)"

lemma baliR_lem: "invc l \<Longrightarrow> invc r \<Longrightarrow> baliR l a r = B l a r"
  apply (induction l a r rule: baliR.induct)
  by auto

lemma baliL_lem: "invc l \<Longrightarrow> invc r \<Longrightarrow> baliL l a r = B l a r"
  apply (induction l a r rule: baliL.induct)
  by auto

lemma "invc t \<Longrightarrow> case ins' x t of None \<Rightarrow> ins x t = t | Some t' \<Rightarrow> ins x t = t'"
  apply(induction x t rule: ins'.induct)
  by (auto split: option.splits simp: baliR_lem baliL_lem)

end