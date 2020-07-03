theory ex10
  imports "HOL-Data_Structures.Tree23_Map" "HOL-Data_Structures.Base_FDS"
begin

datatype 'a trie = Leaf | Node bool "'a \<rightharpoonup> 'a trie"

fun isin:: "'a trie \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isin Leaf _ = False"
| "isin (Node b m) ks = 
     (case ks of [] \<Rightarrow> b
              | k#ks' \<Rightarrow>
                 case m k of None \<Rightarrow> False
                           | Some t \<Rightarrow> (isin t ks'))"

(*fun isin:: "'a trie \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isin Leaf _ = False"
| "isin (Node b m) [] = b"
| "isin (Node b m) (k#ks') = (case m k of None \<Rightarrow> False
                                   | Some t \<Rightarrow> (isin t ks'))"*)

term "(m:: nat \<rightharpoonup> nat trie)(3 \<mapsto> (Node False Map.empty))"

fun ins:: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
  "ins [] Leaf = Node True (Map.empty)"
| "ins (k#ks) Leaf = Node False (Map.empty(k \<mapsto> (ins ks Leaf)))"
| "ins [] (Node b m) = Node True m"
| "ins (k#ks) (Node b m) = (case m k of Some t \<Rightarrow> Node b (m(k \<mapsto> (ins ks t)))
                                        | None \<Rightarrow> Node b (m(k \<mapsto> (ins ks Leaf))))"

lemma ins_correct: "isin (ins as t) bs = (as=bs \<or> isin t bs)"
  apply(induction as t arbitrary: bs rule: ins.induct)
  by (auto split: list.splits option.splits)

fun delete :: "'a list \<Rightarrow> 'a trie \<Rightarrow> 'a trie" where
  "delete _ Leaf = Leaf"
| "delete [] (Node b m) = (Node False m)"
| "delete (k#ks) (Node b m) = (case m k of None \<Rightarrow> (Node b m)
                                         | Some t \<Rightarrow> (Node b (m(k \<mapsto> delete ks t))))"
lemma "isin (delete as t) bs = (as \<noteq> bs \<and> isin t bs)"
  apply(induction as t arbitrary: bs rule: ins.induct)
  by (auto split: list.splits option.splits)

abbreviation "empty23 \<equiv> Tree23.Leaf"
abbreviation "inv23 t \<equiv> complete t \<and> sorted1 (inorder t)"

datatype 'a trie' = Leaf' | Node' bool "('a\<times> 'a trie' ) tree23"

fun isin':: "'a::linorder trie' \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isin' Leaf' _ = False"
| "isin' (Node' b m) ks = 
     (case ks of [] \<Rightarrow> b
              | k#ks' \<Rightarrow>
                 case lookup m k of None \<Rightarrow> False
                           | Some t \<Rightarrow> (isin' t ks'))"

fun ins':: "'a::linorder list \<Rightarrow> 'a trie' \<Rightarrow> 'a trie'" where
  "ins' [] Leaf' = Node' True empty23"
| "ins' (k#ks) Leaf' = Node' False (update k (ins' ks Leaf') empty23)"
| "ins' [] (Node' b m) = Node' True m"
| "ins' (k#ks) (Node' b m) = (case lookup m k of Some t \<Rightarrow> Node' b (update k (ins' ks t) m)
                                        | None \<Rightarrow> Node' b (update k (ins' ks Leaf') m))"

fun delete' :: "'a::linorder list \<Rightarrow> 'a trie' \<Rightarrow> 'a trie'" where
  "delete' _ Leaf' = Leaf'"
| "delete' [] (Node' b m) = (Node' False m)"
| "delete' (k#ks) (Node' b m) = (case lookup m k of None \<Rightarrow> (Node' b m)
                                         | Some t \<Rightarrow> (Node' b (update k (delete' ks t) m)))"


term "size_tree23"

lemma [simp]: "lookup m x = Some xa \<Longrightarrow> size xa < Suc (size_tree23 (\<lambda>x. Suc (size (snd x))) m)"
  apply(induction m)
    apply (auto split: if_splits)
  done


fun trie'_inv where
  "trie'_inv Leaf' = True"
| "trie'_inv (Node' b m) = (inv23 m \<and> (\<forall>k t. lookup m k = Some t \<longrightarrow> trie'_inv t))"

find_consts "('a option \<Rightarrow> 'b option)"

fun trie'_\<alpha> where
  "trie'_\<alpha> Leaf' = Leaf"
| "trie'_\<alpha> (Node' b m) = Node b (map_option trie'_\<alpha> o (lookup m))"

lemmas map23_thms[simp] = M.map_empty Tree23_Map.M.map_update Tree23_Map.M.map_delete
Tree23_Map.M.invar_empty Tree23_Map.M.invar_update Tree23_Map.M.invar_delete
M.invar_def M.inorder_update M.inorder_inv_update sorted_upd_list


lemma isin'_refine: "trie'_inv t \<Longrightarrow> isin' t ks \<longleftrightarrow> isin (trie'_\<alpha> t) ks"
  apply (induction t ks rule: isin'.induct)
  by (auto split: list.splits option.splits)

thm ins_correct

declare[[names_short]]

lemma ins'_refine: "trie'_inv t \<Longrightarrow> ins xs (trie'_\<alpha> t) = trie'_\<alpha> (ins' xs t) \<and> trie'_inv (ins' xs t)"
  apply(induction xs t rule: ins'.induct)
  by (auto split: option.splits)


lemma ins'_correct: "trie'_inv t \<Longrightarrow> 
         (isin' (ins' xs t) ks \<longleftrightarrow> xs=ks \<or> isin' t ks) \<and> trie'_inv (ins' xs t)"
  apply(simp add: isin'_refine ins_correct[symmetric] ins'_refine)
  done



end