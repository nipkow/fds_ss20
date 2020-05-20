theory ex04
  imports "Demos/BST_Demo"
begin

fun in_range :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "in_range \<langle>\<rangle> _ _ = []" | 
  "in_range (Node l a r) u v = 
    (if u < a then in_range l u v else []) @
    (if u \<le> a \<and> a \<le> v then [a] else []) @
    (if a < v then in_range r u v else [])
"

value "set_tree (Node (Node (Node \<langle>\<rangle> (1::nat) \<langle>\<rangle>) 2 (Node \<langle>\<rangle> (3::nat) \<langle>\<rangle>)) 4 (Node \<langle>\<rangle> (5::nat) \<langle>\<rangle>))"

lemma "bst t \<Longrightarrow> set (in_range t u v) = {x \<in>set_tree t. u\<le>x \<and> x \<le>v }"
  apply(induction t)
  apply auto
  done

thm filter_empty_conv

lemma [simp]: "[x] = xs @ x # ys \<longleftrightarrow> xs = [] \<and> ys = []"
  apply (induction xs)
   apply auto
  done

lemma [simp]: "[] = filter P xs \<longleftrightarrow> filter P xs = []"
  apply (induction xs)
   apply auto
  done


lemma "bst t \<Longrightarrow> in_range t u v = filter (\<lambda>x . u\<le>x \<and> x \<le>v ) (inorder t)"
  apply(induction t)
   apply (fastforce simp: filter_empty_conv)+
  done

text \<open>A version that needs less lemmas:\<close>

fun in_range' where
  "in_range' Leaf u v = []"
| "in_range' (Node l x r) u v =
      (if u < x \<and> x < v then in_range' l u v @ x # in_range' r u v
      else if u \<le> x \<and> x < v then x # in_range' r u v
      else if u < x \<and> x \<le> v then in_range' l u v @ [x]
      else if x < u then in_range' r u v
      else if v < x then in_range' l u v
      else if x = u \<and> x = v then [x]
      else []
      )"

lemma "bst t \<Longrightarrow> set (in_range' t u v) = {x\<in>set_tree t. u\<le>x \<and> x\<le>v}"
  apply (induction t)
   apply auto
  done

lemma "bst t \<Longrightarrow> in_range' t u v = filter (\<lambda>x. u\<le>x \<and> x\<le>v) (inorder t)"
  apply (induction t)
   apply (auto simp: filter_empty_conv)
  done

term "()"

term "(\<union>)"

fun enum :: "nat \<Rightarrow> unit tree set" where
  "enum 0 = {}" |
  "enum (Suc n) = enum n \<union> {Node l () r | l r. l \<in> enum n \<and> r \<in> enum n}"

find_theorems "_ \<le> _ \<Longrightarrow> _ \<le> Suc _"

lemma enum_sound: "t \<in> enum n \<Longrightarrow> height t \<le> n"
  apply(induction n arbitrary: t)
   apply (auto simp: le_SucI)
  done

text \<open>The correct definition of enum is below and the one above is the one is developed during the tutorial.
            One cannot tell there is a mistake since the soundness theorem does not properly cover that mistake.
            This shows how underspecifying formal properties can lead to missing bugs....
            \<close>

fun enum' :: "nat \<Rightarrow> unit tree set" where
  "enum' 0 = {Leaf}" |
  "enum' (Suc n) = enum' n \<union> {Node l () r | l r. l \<in> enum' n \<and> r \<in> enum' n}"

end