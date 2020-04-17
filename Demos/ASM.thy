section "Stack Machine and Compilation"

theory ASM
imports AExp
begin

subsection "Stack Machine"

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk  =  " |
"exec1 (LOAD x) s stk  =  " |
"exec1  ADD _ (i # j # stk)  =  "

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = "

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"


subsection "Compilation"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = " |
"comp (V x) = " |
"comp (Plus e1 e2) ="

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s [] = "
apply(induction)
apply (auto)
done

end
