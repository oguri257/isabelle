theory ex3_12
imports AExp BExp begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
type_synonym reg = nat

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec0 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 (LDI0 n) s rs = rs(0:= n)" |
"exec0 (LD0 x ) s rs = rs(0:= s x)" |
"exec0 (ADD0 r) s rs = rs(0:= (rs 0) + (rs r))" |
"exec0 (MV0 r ) s rs = rs(r:= (rs 0)) "

fun exec :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> (reg \<Rightarrow> int)" where
"exec [] _ rs = rs" |
"exec (i#is) s rs = exec is s (exec0 i s rs)"

fun comp0 ::  "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) r = [LDI0 n] @ [MV0 r]" |
"comp0 (V x) r = [LD0 x] @ [MV0 r]" |
"comp0 (Plus e1 e2) r = comp0 e1 r @ [MV0 (r+1)] @ comp0 e2 (r+2) @ [ADD0 (r+1)] @ [MV0 r]"

lemma [simp]: "exec (xs @ ys) s rs = exec ys s (exec xs s rs)"
  apply(induction xs arbitrary: rs)
  apply(auto)
  done

lemma [simp]:"0 < r & r < k \<Longrightarrow> exec (comp0 a k) s rs r = rs r"
  apply (induction a arbitrary:rs r k)
  apply (auto)
  done

theorem "exec (comp0 a r) s rs 0 = aval a s"
  apply(induction a arbitrary:rs r)
  apply(auto)
  done 

end