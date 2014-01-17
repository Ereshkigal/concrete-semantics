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

(* 2.10 *)

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 0" |
"nodes (Node l r) = Suc((nodes l) + (nodes r))"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" | 
"explode (Suc n) t = explode n (Node t t)"

lemma explode_nodes: "nodes (explode n t) =  (2^n) * (nodes t) + 2^n - 1"
apply(induction n arbitrary: t)
apply(auto simp add: algebra_simps)
done

(* 2.11 *)

datatype exp = Const int | Var | Add exp exp | Mul exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval (Const a) x = a" |
"eval Var x = x" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mul a b) x = (eval a x) * (eval b x)" 

fun dot_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"dot_add [] x = x" |
"dot_add x [] = x" |
"dot_add (x # xs) (y # ys) = (x + y) # (dot_add xs ys)"

fun mul_const :: "int \<Rightarrow> int list \<Rightarrow> int list" where 
"mul_const a [] = []" |
"mul_const a (x # xs) = (a * x) # (mul_const a xs)"

fun dot_mul :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"dot_mul [] x = []" |                               
"dot_mul (x # xs) ys = dot_add (mul_const x ys) (0 # (dot_mul xs ys))"  

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs (Const a) = [a]" |
"coeffs Var = []" |
"coeffs (Add x y) = dot_add (coeffs x) (coeffs y)" |
"coeffs (Mul x y) = dot_mul (coeffs x) (coeffs y)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (y # ys) x = y + x * (evalp ys x)"

lemma common_div: "(a::int) * x + a * y = a*(x+y)"
apply(auto simp add: algebra_simps)
done

lemma dotadd_evalp[simp]: "evalp (dot_add as bs) k = evalp as k + evalp bs k"
apply(induction as bs rule: dot_add.induct)
apply(auto simp add: common_div)
done

lemma mulconst_evalp[simp]: "evalp (mul_const a xs) k = a * evalp xs k"
apply(induction xs)
apply(auto simp add: algebra_simps)
done 

lemma dotmul_evalp[simp]: "evalp (dot_mul xs ys) k = (evalp xs k) * (evalp ys k)"
apply(induction xs)
apply(auto simp add: algebra_simps)
done

end
