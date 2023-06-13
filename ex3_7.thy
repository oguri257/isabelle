theory ex3_7
imports BExp
begin

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (less a2 a1)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 =And (Le a1 a2) (Le a2 a1) "

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply(auto)
done

lemma "bval (Le a1 a2) s = (aval a1 s <= aval a2 s)"
apply(auto)
done

end
