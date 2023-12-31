theory BExp imports AExp begin

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n\<^sub>1) (N n\<^sub>2) = Bc(n\<^sub>1 < n\<^sub>2)"|
"less n\<^sub>1 n\<^sub>2 = Less n\<^sub>1 n\<^sub>2"

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction a1 a2 rule: less.induct)
apply auto
done

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and n\<^sub>1 n\<^sub>2 = And n\<^sub>1 n\<^sub>2"

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

theorem "bval (bsimp b) s = bval b s"
apply(induction b)
apply auto
  done

end
