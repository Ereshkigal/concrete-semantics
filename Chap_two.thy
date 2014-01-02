header {* Solutions to Chapter 2 of "Concrete Semantics" *}

theory Chap_two imports Main begin

declare [[names_short]]

(* 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

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

(* 2.3 *)

fun count_e :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count_e y [] = 0" |
"count_e y (x # xs) = (if x = y then Suc(count_e y xs) else count_e y xs)"

lemma count_less: "count_e y xs \<le> length xs"
apply(induction xs)
apply(auto)
done

(* 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a => 'a list" where
"snoc [] y = [y]" |
"snoc (x # xs) y = x # (snoc xs y)" 

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = snoc (rev xs) x"

lemma snoc_cons[simp]: "snoc (y # ss) a = y # (snoc ss a)"
apply(auto)
done

lemma rev_snoc: "rev (snoc xs y) = y # rev xs"
apply(induction xs)
apply(auto)
done

end

