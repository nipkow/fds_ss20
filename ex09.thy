theory ex09
  imports "HOL-Data_Structures.Tree23_Set"
begin

fun joinL where
  "joinL l x r =
     (if height l = height r then
       OF l x r
     else
       case r of
         Node2 t1 v t2 \<Rightarrow>
           case joinL l x t1 of
             TI t \<Rightarrow> TI (Node2 t v t2)
           | OF l' x' r' \<Rightarrow> TI (Node3 l' x' r' v t2)
        | Node3 t1 v1 t2 v2 t3 \<Rightarrow>
           case joinL l x t1 of
             TI t \<Rightarrow> TI (Node3 t v1 t2 v2 t3)
           | OF l' x' r' \<Rightarrow> OF (Node2 l' x' r') v1 (Node2 t2 v2 t3)
           )"

lemma complete_joinL: "\<lbrakk> complete l ; complete r ; height l \<le> height r \<rbrakk> \<Longrightarrow>
                       complete (treeI (joinL l x r )) \<and> height(joinL l x r ) = height r"
  by (induction r) (auto split: upI.splits)

lemma inorder_joinL: "\<lbrakk>complete l ; complete r ; height l \<le> height r \<rbrakk> \<Longrightarrow> 
           inorder (treeI (joinL l x r )) = inorder l @x # inorder r"
  by (induction r) (auto split: upI.splits)


fun joinR where
  "joinR l x r =
     (if height l = height r then
       OF l x r
     else
       case l of
         Node2 t1 v t2 \<Rightarrow>
           case joinR t2 x r of
             TI t \<Rightarrow> TI (Node2 t1 v t)
           | OF l' x' r' \<Rightarrow> TI (Node3 t1 v l' x' r')
        | Node3 t1 v1 t2 v2 t3 \<Rightarrow>
           case joinR t3 x r of
             TI t \<Rightarrow> TI (Node3 t1 v1 t2 v2 t)
           | OF l' x' r' \<Rightarrow> OF (Node2 t1 v1 t2) v2 (Node2 l' x' r')
           )"

lemma complete_joinR: "\<lbrakk> complete l ; complete r ; height l \<ge> height r \<rbrakk> \<Longrightarrow>
                       complete (treeI (joinR l x r )) \<and> height(joinR l x r ) = height l"
  by (induction l) (auto split: upI.splits)

lemma inorder_joinR: "\<lbrakk>complete l ; complete r ; height l \<ge> height r \<rbrakk> \<Longrightarrow> 
           inorder (treeI (joinR l x r )) = inorder l @x # inorder r"
  by (induction l) (auto split: upI.splits)

fun join where
  "join l x r = 
     (if height l \<le> height r then
        treeI (joinL l x r)
      else treeI (joinR l x r))"

thm conjunct1

lemma "complete l \<Longrightarrow> complete r \<Longrightarrow> complete (join l x r)"
  using conjunct1[OF complete_joinL] conjunct1[OF complete_joinR]
  by fastforce+


lemma "complete l \<Longrightarrow> complete r \<Longrightarrow> inorder (join l x r ) = inorder l @x # inorder r"
  using inorder_joinL inorder_joinR
  by fastforce+


end