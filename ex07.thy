theory ex07
  imports Main "HOL-Data_Structures.Sorting" "HOL-Library.Tree"
begin

definition closer where
  "closer b a c = Some(case c of None \<Rightarrow> a 
                               | Some v \<Rightarrow> (if abs (b - a) \<le> abs (b - v) then a else v))"

fun round :: "int tree \<Rightarrow> int \<Rightarrow> int option" where
  "round \<langle>\<rangle> _ = None"
| "round (Node l a r) b = 
    (if a = b then
       Some a
     else if b < a then
       closer b a (round l b)
     else 
       closer b a (round r b)
     )"

lemma [simp]: "round t b = None \<longleftrightarrow> t = \<langle>\<rangle>"
  apply (induction t)
   apply (auto simp: closer_def)
  done

lemma "round t b = Some c \<Longrightarrow> c \<in> set_tree t"
  apply (induction t)
   apply (auto split: if_splits option.splits simp: closer_def)
  done

lemma "bst t \<Longrightarrow> round t b = Some c \<Longrightarrow> a \<in> set_tree t \<Longrightarrow> abs(b - c) \<le> abs (b - a)"
  apply (induction t b arbitrary: c rule: round.induct)
   apply (fastforce split: if_splits option.splits simp: closer_def)+
  done

fun t_round :: "int tree \<Rightarrow> int \<Rightarrow> nat" where
  "t_round \<langle>\<rangle> _ = 1"
| "t_round (Node l a r) b = 
    (if a = b then
       1
     else if b < a then
       1 + (t_round l b)
     else 
       1 + (t_round r b)
     )"

value "t_round \<langle>\<rangle> (-1)"

lemma "t_round t b \<le> height t + 1"
  apply(induction t)
  apply auto
  done

type_synonym intervals = "(nat*nat) list"

fun inv' where
  "inv' _ [] = True"
| "inv' n (iv#ivs) = (case iv of (l, h) \<Rightarrow> n \<le> l \<and> l \<le> h \<and> inv' (Suc (Suc h)) ivs )"

definition inv where "inv \<equiv> inv' 0"

fun set_of where
  "set_of [] = {}"
| "set_of (iv#ivs) = (case iv of (l,h) \<Rightarrow> {l..h} \<union> set_of ivs)"

fun merge_ivs where
  "merge_ivs (l,h) [] = [(l, h)]"
| "merge_ivs (l,h) (iv'#ivs') = 
         (case iv' of (l', h') \<Rightarrow>
            if l' = Suc h then (l, h') # ivs' else (l, h)#(iv'#ivs'))"

fun add where
  "add a [] = (a,a)#[]"
| "add a (iv#ivs) = (case iv of (l, h) \<Rightarrow> 
    if l \<le> a \<and> a \<le> h then
     (l,h)#ivs
   else if Suc a = l then
     (a,h)#ivs
   else if Suc (Suc a) \<le> l then
     (a,a)#(l, h)#ivs
   else if a = Suc h then
     merge_ivs (l, Suc h) ivs
   else iv # (add a ivs)
)"

value "add (1::nat) [(0,0), (3,3)]"

value "merge_ivs (0::nat, 0::nat) [(2, 3)]"

value "(add 1 [(0, 0::nat), (2, 3)])"

declare [[names_short]]

lemma add_correct_aux:
  shows "\<lbrakk>inv' n ivs; n \<le> x\<rbrakk> \<Longrightarrow> inv' n (add x ivs)"
proof (induction ivs arbitrary: n)
  case Nil
  then show ?case
    by (auto simp: inv_def)
next
  case (Cons a ivs)
  then show ?case
    apply(cases ivs)
     apply auto
    done
qed

lemma add_correct:
  shows "inv ivs \<Longrightarrow> inv (add x ivs)"
  using add_correct_aux
  by (auto simp: inv_def)

lemma [simp]: "a \<le> b \<Longrightarrow> inv' (Suc b) ivs \<Longrightarrow> set_of (merge_ivs (a, b) ivs) = {a..b} \<union> set_of ivs" 
  apply (cases ivs)
  apply (auto split: if_splits)
  done

lemma add_correct_2_aux:
  shows "inv' m ivs  \<Longrightarrow> set_of (add x ivs) = insert x (set_of ivs)"
  apply (induction m ivs rule: inv'.induct)
   apply (auto split: if_splits)
  done
  


lemma add_correct_2:
  shows "inv ivs \<Longrightarrow> set_of (add x ivs) = insert x (set_of ivs)"
  using add_correct_2_aux
  by (auto simp: inv_def)

end