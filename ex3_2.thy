theory ex3_2
imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N (i\<^sub>1+i\<^sub>2)"|
"plus (N i) a = (if i=0 then a else Plus (N i) a)"|
"plus a (N i) = (if i=0 then a else Plus a (N i))"|
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"

fun sum_n :: "aexp \<Rightarrow> int" where
"sum_n (N a) = a" |
"sum_n (Plus a b) = (sum_n a) + (sum_n b)" |
"sum_n (V x) = 0"

fun sum_v :: "aexp \<Rightarrow> aexp" where 
"sum_v  (N a) = N 0" |
"sum_v  (Plus a b) = Plus (sum_v a) (sum_v b)" |
"sum_v  (V x) = V x"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (Plus (sum_v a) (N (sum_n a)))"

lemma aval_plus [simp]:"aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply(auto)
done

lemma "aval (full_asimp a) s = aval a s"
apply(induction a)
apply(auto)
done

value "full_asimp (Plus (Plus (N 0) (N 7)) (Plus (V x) (N 8)))"

end
