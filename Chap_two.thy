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

fun rev2 :: "'a list \<Rightarrow> 'a list" where
"rev2 [] = []" |
"rev2 (x # xs) = snoc (rev2 xs) x"

lemma snoc_cons[simp]: "snoc (y # ss) a = y # (snoc ss a)"
apply(auto)
done

lemma rev2_snoc[simp]: "rev2 (snoc xs y) = y # rev2 xs"
apply(induction xs)
apply(auto)
done

lemma rev2_rev2: "rev2 (rev2 xs) = xs"
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

(* 2.7 *)

datatype 'a tree2 = Tip 'a | Right 'a "'a tree2" | Left 'a "'a tree2" | Node "'a tree2" 'a "'a tree2"

fun rev :: "'a list => 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = (rev xs) @ (Cons x Nil)"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Right a r) = Left a (mirror r)" |
"mirror (Left a l) = Right a (mirror l)" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = [a]" |
"pre_order (Right a r) = a # (pre_order r)" |
"pre_order (Left a l) = a # (pre_order l)" |
"pre_order (Node l a r) = a # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = [a]" |
"post_order (Right a r) = (post_order r) @ [a]" |
"post_order (Left a l) = (post_order l) @ [a]" |
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

lemma rev_lemm[simp]: "rev (a @ b) = (rev b) @ (rev a)"
apply(induction a)
apply(auto)
done

lemma rev_order: "pre_order (mirror t) = rev (post_order t)"
apply(induction t)
apply(auto)
done

(* 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # xs) = [a, x] @ (intersperse a xs)"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs) 
apply(auto)
done

(* 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma add_itadd: "itadd m n = add m n"
apply(induction m arbitrary: n)
apply(auto)
done


