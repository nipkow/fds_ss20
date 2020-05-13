theory ex03
  imports "BST_Demo"
begin

thm isin.simps

fun isin2 :: "('a::linorder) tree \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" where
"isin2 Leaf z x = (case z of None \<Rightarrow> False | Some y \<Rightarrow> x = y)" |
"isin2 (Node l a r) z x =
  (if x < a then isin2 l z x
   else isin2 r (Some a) x)"

lemma isin2_Some:
"\<lbrakk>bst t; \<forall>x\<in>set_tree t. a < x\<rbrakk> \<Longrightarrow>
   isin2 t (Some a) x = (isin t x \<or> a = x)"
  apply(induction t arbitrary: a)
  apply auto
  done

lemma isin2_None:
"bst t \<Longrightarrow> isin2 t None x = isin t x"
  apply(induction t)
   apply (auto simp add: isin2_Some)
  done

fun join :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "join t \<langle>\<rangle> = t" |
  "join \<langle>\<rangle> t = t" |
  "join (Node l1 a1 r1) (Node l2 a2 r2) = 
     (case join r1 l2 of \<langle>\<rangle> \<Rightarrow> Node l1 a1 (Node \<langle>\<rangle> a2 r2)
                  | Node l a r \<Rightarrow> Node (Node l1 a1 l) a (Node r a2 r2))"

value "join (Node (Node \<langle>\<rangle> (1::nat) \<langle>\<rangle>) 2 (Node \<langle>\<rangle> (3::nat) \<langle>\<rangle>)) (Node (Node \<langle>\<rangle> (4::nat) \<langle>\<rangle>) 5 (Node \<langle>\<rangle> (6::nat) \<langle>\<rangle>))"

thm tree.splits

lemma join_inorder: "inorder (join t1 t2 ) = inorder t1 @ inorder t2"
  apply(induction t1 t2 rule: join.induct)
    apply (auto split: tree.splits)
  done

lemma "height(join t1 t2 ) \<le> max (height t1 ) (height t2 ) + 1"
  apply(induction t1 t2 rule: join.induct)
    apply (auto split: tree.splits)
  done

thm set_inorder[symmetric]

thm set_append

lemma set_tree_join: "set_tree (join t1 t2 ) = set_tree t1 \<union> set_tree t2"
  by (auto simp del: set_inorder simp: set_inorder[symmetric] join_inorder)

thm bst_iff_sorted_wrt_less
thm sorted_wrt_append

lemma bst_join: "bst (Node l (x ::'a::linorder ) r ) \<Longrightarrow> bst (join l r )"
  apply(auto simp del: bst_wrt.simps
             simp: bst_iff_sorted_wrt_less join_inorder sorted_wrt_append)
  done

fun delete:: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "delete x \<langle>\<rangle> = \<langle>\<rangle>" |
  "delete x (Node l a r) = 
   (if x = a then join l r else
    if x < a then Node (delete x l) a r else
    Node l a (delete x r))"

declare join.simps [simp del]

lemma [simp]: "bst t \<Longrightarrow> set_tree (delete x t) = (set_tree t)- {x}"
  apply (induction t)
   apply (auto simp: set_tree_join)
  done

lemma "bst t \<Longrightarrow> bst (delete x t)"
  apply (induction t)
  apply(auto simp: bst_join)
  done

end