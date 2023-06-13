theory Ex2_2
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02[simp]: "add m 0 = m"
apply(induction m)
apply(auto)
done

lemma add_asso: "add (add x y) z = add x (add y z)"
apply(induction x)
apply(auto)
done

lemma add_comm2[simp]: "Suc (add x y) = add x (Suc y)"
apply(induction x)
apply(auto)
done

lemma add_comm: "(add x y) = (add y x)"
apply(induction x)
apply auto
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc(Suc (double m))"

lemma double_add : "double x = add x x"
apply(induction x)
apply(auto)
done

end
