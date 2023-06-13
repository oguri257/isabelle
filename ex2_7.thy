theory ex2_7
imports Main
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Leaf = Leaf" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Leaf =[]" |
"pre_order (Node l x r) = [x]@(pre_order l)@(pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Leaf = []" |
"post_order (Node l x r) = (post_order l)@(post_order r)@[x]"

value "mirror(Node (Node Leaf a Leaf) b t)"
value "pre_order (Node (Node Leaf a Leaf) b t)"
value "post_order (Node (Node Leaf a Leaf) b t)"

lemma order : "pre_order (mirror t) = rev (post_order t)"
apply (induction t)
apply (auto)
done

end