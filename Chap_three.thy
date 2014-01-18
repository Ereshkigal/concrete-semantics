header {* Solutions to Chapter 3 of "Concrete Semantics" *}

theory Chap_three imports Main begin

declare [[names_short]]

(* 3.1 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N a) = N a" |
"asimp_const (V x) = V x" |
"asimp_const (Plus p q) = 
 (case (asimp_const p, asimp_const q) of 
  (N a, N b) \<Rightarrow> N (a+b) |
  (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N a) (N b)) = False" |
"optimal (Plus a b) = (optimal a \<and> optimal b)"

lemma "optimal (asimp_const p)"
apply(induction p)
apply(auto split: aexp.split)
done

(* 3.2 *)

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N a) = N a" |
"full_asimp (V x) = V x" |
"full_asimp (Plus p q) = 
 (case (full_asimp p, full_asimp q) of
  (Plus x (N a), Plus y (N b)) \<Rightarrow> Plus (Plus x y) (N (a+b)) |
  (N a, N b) \<Rightarrow> N (a+b) |
  (Plus x (N a), N b) \<Rightarrow> Plus x (N (a+b)) |
  (N a, Plus x (N b)) \<Rightarrow> Plus x (N (a+b)) |
  (Plus x (N a), y) \<Rightarrow> Plus (Plus x y) (N a) |
  (x, Plus y (N a)) \<Rightarrow> Plus (Plus x y) (N a) |
  (N a, x) \<Rightarrow> Plus x (N a) |
  (x, y) \<Rightarrow> Plus x y)"

lemma "aval (full_asimp x) s = aval x s"
apply(induction x)
apply(auto split: aexp.split)
done

(* 3.3 *)

end
