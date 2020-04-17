theory BExp imports AExp begin

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
            <''x'' := 3, ''y'' := 1>"


subsection "Constant Folding"

text \<open>Optimizing constructors:\<close>

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less "

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction)
apply auto
done

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and = "

lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
apply(induction b1 b2 rule: and.induct)
apply auto
done

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc v) = Bc(\<not> v)" |
"not b = Not b"

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
apply(induction )
apply auto
done

text \<open>Now the overall optimizer:\<close>

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)" |
"bsimp (Less a\<^sub>1 a\<^sub>2) = less (asimp a\<^sub>1) (asimp a\<^sub>2)"

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

theorem "bval (bsimp b) s = bval b s"
apply(induction b)
apply auto
done

end
