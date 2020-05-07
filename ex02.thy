theory ex02
  imports Main
begin


fun list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0" |
  "list_sum (x # xs) = x + list_sum xs"

value "list_sum [1,2,3]"

thm fold.simps

definition list_sum'::"nat list \<Rightarrow> nat" where
  "list_sum' xs \<equiv> fold (+) xs (0::nat)"

value "list_sum' [1,2,3]"

thm list_sum'_def

lemma lemma_aux: "fold (+) xs a = list_sum xs + a"
  apply(induction xs arbitrary: a)
   apply auto
  done


lemma "list_sum xs = list_sum' xs"
  apply (auto simp: list_sum'_def lemma_aux)
  done

datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree"

fun inorder::"'a ltree \<Rightarrow> 'a list" where
  "inorder (Leaf x) = [x]" |
  "inorder (Node l r) = inorder l @ inorder r"

value "inorder (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3))"

term "fold f (inorder t) s"

value "fold (+) (inorder (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3))) 0"

fun fold_ltree:: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" where
  "fold_ltree f (Leaf x) s = f x s" |
  "fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)"

value "fold_ltree (+) (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3)) 0"

lemma "fold f (inorder t) s = fold_ltree f t s"
  apply(induction t arbitrary: s)
   apply auto
  done

fun mirror:: "'a ltree \<Rightarrow> 'a ltree" where
  "mirror (Leaf x) = Leaf x" | 
  "mirror (Node l r) = (Node (mirror r) (mirror l))"

value "inorder (mirror (Node (Node (Leaf (1::nat)) (Leaf 2)) (Leaf 3)))"

lemma "inorder (mirror t) = rev (inorder t)"
  apply(induction t)
  apply auto
  done

term "map f xs"

fun shuffles:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "shuffles xs [] = [xs]" |
  "shuffles [] ys = [ys]" |
  "shuffles (x#xs) (y#ys) = map (\<lambda>xs. x # xs) (shuffles xs (y#ys)) @
                            map (\<lambda>ys. y # ys) (shuffles (x#xs) ys)"

thm shuffles.induct

lemma "zs \<in> set (shuffles xs ys) \<Longrightarrow> length zs = length xs + length ys"
  apply(induction xs ys arbitrary: zs rule: shuffles.induct)
    apply auto
  done

end

