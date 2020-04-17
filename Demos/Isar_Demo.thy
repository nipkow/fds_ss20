theory Isar_Demo
imports Complex_Main
begin

section "An introductory example"

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text \<open>A bit shorter:\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from 1 show "False" by blast
qed

subsection \<open>"this", "then", "hence" and "thus\<close>

text \<open>Avoid labels, use "this"\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text \<open>"then" = "from this"\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then show "False" by blast
qed

text \<open>"hence" = "then have", "thus" = "then show"\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed


subsection \<open>Structured statements: "fixes", "assumes", "shows"\<close>

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -  (* no automatic proof step! *)
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed


section "Proof patterns"

lemma "P \<longleftrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

lemma "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

text "Contradiction"

lemma P
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

text "Case distinction"

lemma "R"
proof cases
  assume "P"
  show "R" sorry
next
  assume "\<not> P"
  show "R" sorry
qed

lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed


text \<open>"obtain" example\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


text \<open>Interactive exercise:\<close>

lemma assumes "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
sorry


subsection \<open>(In)Equation Chains\<close>

lemma "(0::real) \<le> x^2 + y^2 - 2*x*y"
proof -
  have "0 \<le> (x - y)^2" by simp
  also have "\<dots> = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  finally show "0 \<le> x^2 + y^2 - 2*x*y" .
qed

text \<open>Interactive exercise:\<close>

lemma
  fixes x y :: real
  assumes "x \<ge> y" "y > 0"
  shows "(x - y) ^ 2 \<le> x^2 - y^2"
proof -
  have "(x - y) ^ 2 = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  show "(x - y) ^ 2 \<le> x^2 - y^2" sorry
qed


section "Streamlining proofs"

subsection "Pattern matching and ?-variables"

text \<open>Show \<open>\<exists>\<close>\<close>

lemma "\<exists> xs. length xs = 0" (is "\<exists> xs. ?P xs")
proof
  show "?P([])" by simp
qed

text \<open>Multiple EX easier with forward proof:\<close>

lemma "\<exists> x y :: int. x < z & z < y" (is "\<exists> x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed


subsection "Quoting facts"

lemma assumes "x < (0::int)" shows "x*x > 0"
proof -
  from `x<0` show ?thesis by(metis mult_neg_neg)
qed


subsection "Example: Top Down Proof Development"

lemma "\<exists>ys zs. xs = ys @ zs \<and>
          (length ys = length zs \<or> length ys = length zs + 1)"
sorry



section "Solutions to interactive exercises"

lemma assumes "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix b
  from assms obtain a where 0: "\<forall>y. P a y" by blast
  show "\<exists>x. P x b"
  proof
    show "P a b" using 0 by blast
  qed
qed

lemma fixes x y :: real assumes "x \<ge> y" "y > 0"
shows "(x - y) ^ 2 \<le> x^2 - y^2"
proof -
  have "(x - y) ^ 2 = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  also have "\<dots> \<le> x^2 + y^2 - 2*y*y"
    using assms by(simp)
  also have "\<dots> = x^2 - y^2"
    by(simp add: numeral_eq_Suc)
  finally show ?thesis .
qed

subsection "Example: Top Down Proof Development"

text \<open>The key idea: case distinction on length:\<close>

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "EX n. length xs = n+n"
  show ?thesis sorry
next
  assume "\<not> (EX n. length xs = n+n)"
  show ?thesis sorry
qed

text \<open>A proof skeleton:\<close>

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "\<exists>n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" sorry
  thus ?thesis by blast
next
  assume "\<not> (\<exists>n. length xs = n+n)"
  then obtain n where "length xs = Suc(n+n)" sorry
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" sorry
  then show ?thesis by blast
qed

text "The complete proof:"

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "\<exists>n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs"
    by (simp add: `length xs = n + n`)
  thus ?thesis by blast
next
  assume "\<not> (\<exists>n. length xs = n+n)"
  hence "\<exists>n. length xs = Suc(n+n)" by arith
  then obtain n where l: "length xs = Suc(n+n)" by blast
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: l)
  thus ?thesis by blast
qed

end
