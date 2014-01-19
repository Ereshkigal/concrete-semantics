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

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x p (N a) = N a" |
"subst x p (V y) = (if x = y then p else (V y))" |
"subst x p (Plus q r) = Plus (subst x p q) (subst x p r)"

lemma aval_subst[simp]: "aval (subst x p e) s = aval e (s(x := aval p s))"
apply(induction e)
apply(auto)
done

lemma "aval p s = aval q s \<Longrightarrow> aval (subst x p e) s = aval (subst x q e) s"
apply(auto)
done

(* 3.4 *)

datatype aexpm = N int | V vname | Plus aexpm aexpm | Times aexpm aexpm

fun avalm :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
"avalm (N a) s = a" |
"avalm (V x) s = s x" |
"avalm (Plus a b) s = avalm a s + avalm b s" |
"avalm (Times a b) s = avalm a s * avalm b s"

fun plusm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"plusm (N a) (N b) = N (a+b)" |
"plusm p (N i) = (if i = 0 then p else Plus p (N i))" |
"plusm (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plusm p q = (Plus p q)"

fun timesm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"timesm (N a) (N b) = N (a*b)" |
"timesm p (N i) = (if i = 0 then (N 0) else (if i=1 then p else Times p (N i)))" |
"timesm (N i) p = (if i = 0 then (N 0) else (if i=1 then p else Times (N i) p))" |
"timesm p q = (Times p q)"

fun asimpm :: "aexpm \<Rightarrow> aexpm" where
"asimpm (N a) = N a" |
"asimpm (V x) = V x" |
"asimpm (Plus p q) = plusm (asimpm p) (asimpm q)" |
"asimpm (Times p q) = timesm (asimpm p) (asimpm q)"

lemma avalm_plusm: "avalm (plusm a b) k = avalm a k + avalm b k"
apply(induction a b rule: plusm.induct)
apply(auto)
done 

lemma avalm_timesm: "avalm (timesm a b) k = avalm a k * avalm b k"
apply(induction a b rule: timesm.induct)
apply(auto)
done

lemma "avalm (asimpm p) s = avalm p s"
apply(induction p)
apply(auto simp add: avalm_plusm avalm_timesm)
done

(* 3.5 *)

datatype aexp2 = N int | V vname | Plus aexp2 aexp2 | Times aexp2 aexp2 | PlusPlus vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val * state" where
"aval2 (N a) s = (a, s)" |
"aval2 (V x) s = (s x, s)" |
"aval2 (Plus a b) s = (fst (aval2 a s) + fst (aval2 b (snd (aval2 a s))), snd (aval2 b (snd (aval2 a s))))" |
"aval2 (Times a b) s = (fst (aval2 a s) * fst (aval2 b (snd (aval2 a s))), snd (aval2 b (snd (aval2 a s))))" |
"aval2 (PlusPlus x) s = (s x, s(x := (s x) + 1))" 


end
