theory ex10_2
  imports "Trie1"
begin

fun union::"trie \<Rightarrow> trie \<Rightarrow> trie" where
  "union t Leaf = t"
| "union Leaf t = t"
| "union (Node b1 (l1,r1)) (Node b2 (l2,r2)) = Node (b1 \<or> b2) (union l1 l2, union r1 r2)"

declare[[names_short]]

value "isin (Node True (Leaf, Leaf)) []"

value "isin Leaf []"

lemma "isin (union a b) x = (isin a x \<or> isin b x)"
  apply(induction a b arbitrary: x rule: union.induct)
  by (auto split: list.splits)