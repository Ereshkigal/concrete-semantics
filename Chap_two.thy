header {* Solutions to Chapter 2 of "Concrete Semantics" *}

theory Chap_two imports Main begin

text {*

*}

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

lemma add_nil[simp]: "add b 0 = b"
apply(induction b)
apply(auto)
done

lemma add_sup[simp]: "Suc (add b a) = add b (Suc a)"
apply(induction b)
apply(auto)
done

lemma add_comm: "add a b = add b a"
apply(induction a)
apply(auto)
done

end

