theory Single_Step_Demo
imports Main
begin

text \<open>"thm" is a command that displays one or more named theorems:\<close>
thm conjI impI iffI notI

text \<open>Instantiation of theorems: "of"\<close>

text \<open>Positional:\<close>
thm conjI[of "A" "B"]
thm conjI[of "A"]
thm conjI[of _ "B"]

text \<open>By name:\<close>
thm conjI[where ?Q = "B"]

text \<open>Composition of theorems: "OF"\<close>

thm refl[of "a"]
thm conjI[OF refl[of "a"] refl[of "b"]]
thm conjI[OF refl[of "a"]]
thm conjI[OF _ refl[of "b"]]


text \<open>A simple backward proof:\<close>
lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> A \<and> B"
apply(rule conjI)
apply assumption
apply assumption
done

end
