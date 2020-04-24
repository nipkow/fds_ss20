theory ex01
imports Main
begin

value "2 + (2::nat)"

value "(2::nat) * (5 + 3)"

value "(3::nat) * 4 - 2 *(7 + 1)"

lemma "(x::nat) + (y + z) = (x + y) + z"
  by auto

lemma "(x::nat) + y = y + x"
  apply auto
  done

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x#xs) x' = (if x = x' then Suc (count xs x') else count xs x')"


value "count [(1::nat), 1, 1] 1"

theorem "count xs x \<le> length xs"
  apply(induct xs)
   apply auto
  done

fun snoc::"'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x' = [x']" |
"snoc (x#xs) x' = x # (snoc xs x')"

value "snoc [(1::nat),2,3,4] 5"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" | 
"reverse (x#xs) = snoc (reverse xs) x"

value "reverse [(1::nat),2,3,4]"

lemma "reverse [(1::nat),2,3,4] = [4,3,2,1]"
  by simp

lemma reverse_snoc:
  "reverse (snoc xs y) = y # reverse xs"
  by (induct xs) auto

theorem "reverse (reverse xs) = xs"
  apply(induct xs)
   apply (auto simp add: reverse_snoc)
  done

fun reverse_helper::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"reverse_helper ys [] = ys" |
"reverse_helper ys (x # xs) = reverse_helper (x # ys) xs"

fun reverse'::"'a list \<Rightarrow> 'a list" where
  "reverse' xs = reverse_helper [] xs"

value "reverse' [1,2,3::nat]"

lemma reverse_helper_lem: "reverse_helper [] (reverse_helper ys xs) = reverse_helper xs ys"
  apply (induct xs arbitrary: ys)
   apply auto
  done


lemma "reverse' (reverse' xs) = xs"
  apply(induct xs)
   apply (auto simp: reverse_helper_lem)
  done
end