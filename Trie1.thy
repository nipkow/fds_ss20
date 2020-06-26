(* Author: Tobias Nipkow *)

section "Trie1"

theory Trie1
imports Main
begin

datatype trie = Leaf | Node bool "trie * trie"

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool" where
"isin Leaf ks = False" |
"isin (Node b (l,r)) ks =
   (case ks of
      [] \<Rightarrow> b |
      k#ks \<Rightarrow> isin (if k then r else l) ks)"
end
