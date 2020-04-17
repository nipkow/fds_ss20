theory List_Demo
imports Main
begin

datatype 'a list = Nil | Cons "'a" "'a list"

term "Nil"

(* In this special situation: *)
declare [[names_short]]

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = xs"

value "rev(Cons True (Cons False Nil))"

value "rev(Cons a (Cons b Nil))"

theorem rev_rev: "rev (rev xs) = xs"
apply (induction xs)
apply (auto)
done

end
