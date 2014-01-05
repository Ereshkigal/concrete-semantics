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

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double n = add n n"
apply(induction n)
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

lemma rev_snoc[simp]: "rev (snoc xs y) = y # rev xs"
apply(induction xs)
apply(auto)
done

lemma rev_rev: "rev (rev xs) = xs"
apply(induction xs)
apply(auto)
done

(* 2.5 *)

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = add (Suc n) (sum n)"

lemma add_mul2[simp]: "add n (m div 2) = (2*n + m) div 2"
apply(induction n)
apply(auto)
done

lemma sum_is: "sum n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

(* 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil" |
"contents (Node l a r) = a # ((contents l) @ (contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node l a r) = a + (treesum l) + (treesum r)"

lemma tree_list: "treesum x = listsum (contents x)"
apply(induction)
apply(auto)
done



end

