theory ex06
imports Main
begin

fun reverse where
  "reverse [] = []"
| "reverse (x # xs) = reverse xs @ [x]"

thm append.simps

fun t_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_append [] _ = 0"
| "t_append (x # xs) ys = 1 + t_append xs ys"

fun t_reverse where
  "t_reverse [] = 0"
| "t_reverse (x # xs) = t_append (reverse xs) [x] + t_reverse xs + 1"

value "replicate (4::nat) (()::unit)"

value "map (\<lambda>x. t_reverse (replicate x (()::unit))) [0::nat, 1, 2, 3, 4, 5, 6]"

lemma [simp]: "t_append xs [a] = length xs"
  by (induction xs) auto

lemma [simp]: "length (reverse xs) = length xs"
  by (induction xs) auto

find_theorems "((_::nat) - _) + _"

lemma "t_reverse xs = (length xs * (length xs + 1)) div 2"
  by (induction xs) auto

term sort_key

find_theorems filter insort_key

find_theorems sorted sort_key

find_theorems "?x \<in> set (filter ?P _)" "?P ?x"

lemma "filter (\<lambda>x . k x = a) (sort_key k xs) = filter (\<lambda>x . k x = a) xs"
  apply(induction xs)
   apply (auto simp: filter_insort insort_is_Cons filter_insort_triv)
  done

end