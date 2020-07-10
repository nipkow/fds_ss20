theory ex11
  imports "HOL-Data_Structures.Leftist_Heap"
begin

fun lh_insert::"'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap" where
  "lh_insert x Leaf = Node Leaf (x, 1) Leaf"
| "lh_insert x (Node l (y, k) r) = (if x \<ge> y then (node l y (lh_insert x r))
                                    else (node l x (lh_insert y r)))"


lemma set_lh_insert: "set_tree (lh_insert x t) = set_tree t \<union> {x}"
  apply(induction t arbitrary:x)
   apply (auto split: if_splits simp: node_def)
  done

declare[[names_short]]

value "lh_insert 1 \<langle>\<langle>\<rangle>, (0::nat, 1), \<langle>\<rangle>\<rangle>"

find_theorems "\<forall>_\<in>(_\<union>_). _"

lemma "heap (t::nat lheap) \<Longrightarrow> heap (lh_insert x t)"
  apply(induction t arbitrary: x)
   apply (fastforce simp: node_def set_lh_insert ball_Un)+
  done

lemma "ltree t \<Longrightarrow> ltree (lh_insert x t)"
  apply(induction t arbitrary:x)
   apply (auto split: if_splits simp: node_def)
  done

fun t_lh_insert::"'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat" where
  "t_lh_insert x Leaf = 1"
| "t_lh_insert x (Node l (y, k) r) = 1 + (if x \<ge> y then (t_lh_insert x r)
                                          else (t_lh_insert y r))"

lemma "t_lh_insert x t \<le> rank t + 1"
  apply(induction t arbitrary: x)
   apply auto
  done

find_theorems "(\<in>#)" "(-)::'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset"

datatype ('a, 's) bs_pq = Empty | Heap 'a 's

locale Bs_Priority_Queue =
  orig: Priority_Queue where
    empty = orig_empty and
    is_empty = orig_is_empty and
    insert = orig_insert and
    get_min = orig_get_min and
    del_min = orig_del_min and
    invar = orig_invar and
    mset = orig_mset
  for orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar 
  and orig_mset :: "'s \<Rightarrow> 'a::linorder multiset"
begin

definition empty where
  "empty = Empty"

fun is_empty where
  "is_empty Empty = True"
| "is_empty (Heap _ _) = False "

fun insert where
  "insert x Empty = Heap x orig_empty"
| "insert x (Heap m q) = (if x < m then Heap x (orig_insert m q) else Heap m (orig_insert x q))"

fun get_min where
 "get_min (Heap m _) = m"

fun del_min where
 "del_min (Heap m q) = (if orig_is_empty q then Empty
                        else Heap (orig_get_min q) (orig_del_min q))"

fun invar where
  "invar Empty = True"
| "invar (Heap m q) = ((orig_invar q) \<and> (\<forall>x\<in>set_mset (orig_mset q). m \<le> x))"

fun mset where
  "mset Empty = {#}"
| "mset (Heap m q) = add_mset m (orig_mset q)"

lemmas [simp] = orig.mset_empty orig.is_empty orig.mset_insert orig.mset_del_min
                orig.mset_get_min orig.invar_empty orig.invar_insert orig.invar_del_min

sublocale Priority_Queue where
  empty = empty
  and is_empty=is_empty
  and insert=insert
  and get_min=get_min
  and del_min=del_min
  and invar=invar
  and mset=mset
  apply unfold_locales
proof goal_cases
case 1
  then show ?case
    by (auto simp add: empty_def)
next
  case (2 q)
  then show ?case 
    by (cases q) auto
next
  case (3 q x)
  then show ?case
    by (cases q) auto
next
  case (4 q)
  then show ?case
    by (cases q) auto
next
  case (5 q)
  then show ?case
    by (cases q) (auto simp: Min_insert2)
next
  case 6
  then show ?case 
    by (auto simp: empty_def)
next
  case (7 q x)
  then show ?case
    by (cases q) auto
next
  case (8 q)
  then show ?case
    apply (cases q)
    using in_diffD
    by force+
qed
end

end



end