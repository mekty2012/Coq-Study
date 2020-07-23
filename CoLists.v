(** CoPoly : Polymorphism with CoInduction *)

(* Author : TaeYoung Kim, KAIST SoC *)
(* Last Modify at : Jul 23, 2020. *)

Set Warnings "-notation-overridden,-parsing".

(* In this chapter, we extend our availability on computation by
   introducing infinite data type and lazy computation. The critical 
   idea are coinductive type and cofixpoint. We begin with Coinductive
   List. *)

CoInductive CList (X : Type) : Type :=
| CCons (x : X) (l : CList X) : CList X.

(* As we've done in Poly, set type as implicit argument. *)
Arguments CCons {X} _ _.

(* What is this datatype? A CoList is pair of a
   single data and another CoList. It extends idea of
   list, however it is infinite data type unlike inductive
   list. CoInductive makes us to define possibly 
   infinite data type, like this CList consisting infinite
   number of data type X. *)

(* If you are familar to category theory, we can explain this
   idea formally. An inductive type is initial object of algebra
   category, and coinductive type is final object of coalgebra.
   This is dual of inductive type. In fact, every 'co-' says that
   it is dual of one without 'co-'. You don't need to understand
   this fact to study this section. *)

(* Unlike list, where we could create finite list easily, 
   we can't construct colist by definition. Instead, we need to 
   use cofixpoint. We will see this soon. *)

(* Here, let's just assume some object of colist of nat. *)

Definition mycolist : CList nat. Admitted.

(* We can extend this colist by appending some element. *)

Definition mycolist1 : CList nat :=
  CCons 1 mycolist.

(* Or longer. *)

Definition mycolist2 : CList nat :=
  CCons 3 (CCons 2 (CCons 1 mycolist)).

(* Also we can reduce list as following. *)

Definition mycolist3 : CList nat :=
  match mycolist with
  | CCons _ cl' => cl'
  end.

(* Or extend by arbitrary list of number. *)

Fixpoint append_list {X : Type} (l : list X) (cl : CList X) : CList X :=
  match l with
  | nil => cl
  | cons x l' => append_list l' (CCons x cl)
  end.

(* What this function does is, given some sequence (x1, x2, x3, ...) and 
   finite list (y1, y2, ..., yn) returns another sequence 
   (y1, y2, ..., yn, x1, x2, x3, ...). You can see Fixpoint can be used involving
   CoInductive Type. *)

(* However, since every fixpoint terminates, we can't construct 
   infinite list with fixpoint. So we need dual version. 
   As you may expect, it is so called CoFixpoint. Fixpoint get 
   Inductive type as input, and can return any type. Conversely, 
   CoFixpoint get any type, and can return CoInductive type. *)

CoFixpoint constant {X : Type} (x : X) : CList X :=
  CCons x (constant x).

Definition clist3 := constant 3.

(* So this function creates infinite list only containing x,
   or sequence (x, x, x, ...). This is similar to repeat you
   defined in List, however we do not specify number, since
   it is infinite already. *)

(* How this definition works? This is similar to Fixpoint
   which is recursion, called corecursion. However, unlike
   fixpoint is finite (which is assured by subterm criterion)
   cofixpoint is infinite, so we can't actually compute. *)

(* Instead, CoFixpoint does lazy computation. This means that
   until we actually need value, CoFixpoint becomes lazy, so
   it delays its computation. So we can say that CoList is 
   lazy list. *)

(* Then when we restart computation? this is done when we
   pattern match CoList. *)

Definition head {X : Type} (cl : CList X) : X :=
  match cl with
  | CCons x _ => x
  end.

Definition tail {X : Type} (cl : CList X) : CList X :=
  match cl with
  | CCons _ cl' => cl'
  end.

Eval compute in (head (constant 3)).

(* Since our computation is finite, we only can see finite
   prefix of every colist. So functions that we can define
   can only be defined on finite prefix of colist. This is
   called finiteness property, that finite prefix of result
   is determined by finite prefix of input. Also, this matches
   with notion of continuity in Scott topology. *)

(* To ensure this property, there is constraint for CoFixpoint
   similar to what Fixpoint had, that recursive call should be
   done on its subterm. Every recursive call of CoFixpoint function
   should be capsuled by any of constructor of return type. *)

(* Why should this be ensured? It should be allowed to get finite
   prefix, and to do so, we need to do pattern match, which is possible
   only when we have constructor. *)


(*
   CoFixpoint constant {X : Type} (x : X) : CList X :=
     CCons x (constant x).

   Here, recursive call to constant is capsuled by CCons x.
 *)

(* Now we define function so called prefix, that gets finite prefix of
   colist. This function gives good testing examples.
 *)

Fixpoint prefix {X : Type} (cl : CList X) (n : nat) : list X :=
  match n with
  | 0 => nil
  | S n' =>
    match cl with
    | CCons x cl' => cons x (prefix cl' n')
    end
  end.

Eval compute in (prefix (constant 3) 10).

(* More on cofixpoint *)

(* So we may require some other sequences, like
   (1, 2, 3, ...)
   (true, false, true, false, ...)
   We can implement this idea by following.
   *)

CoFixpoint increase (n : nat) : CList nat := CCons n (increase (S n)).
CoFixpoint alter (b : bool) : CList bool := CCons b (alter (negb b)).

(* Again, recursive call to increase is capsuled by CCons, and
   recursive call to alter is also capsuled. *)

(* Moreover, we can define complex sequences as following, which gives
   another definition of increase and alter. This definition is infinite 
   automata, where X here is state of automata, next is transition function, 
   cur is output transformer. *)

CoFixpoint creater {X Y : Type} (x : X) (cur : X -> Y) (next : X -> X) : CList Y :=
  CCons (cur x) (creater (next x) cur next).

Definition increase1 (n : nat) := creater n (fun n' => n') (fun n' => S n').
Definition alter1 (b : bool) := creater b (fun b' => b') (fun b' => negb b').

(* Define a function skip, that receives two argument CList X and nat
   (x1, x2, ...), n
   and returns CList X
   (xn+1, xn+2, ...)
 *)

Fixpoint skip {X} (cl : CList X) (n : nat) : CList X. Admitted.

(* Define a function alternate that given two colist
   (x1, x2, x3, ...)
   (y1, y2, y3, ...)
   returns
   (x1, y1, x2, y2, x3, y3, ...)
 *)

CoFixpoint alternate {X} (l1 l2 : CList X) : CList X. Admitted.

(* These are functions from Lists.v. For each functions defined here,
   determine whether they can extended to cofixpoint or not. If not, 
   explain why. If can, extend it. You don't need to prove that your
   implementation is correct until now.
 *)

Require Export Coq.Lists.List.
Export ListNotations.

(*
Fixpoint length (l:list nat) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint nonzeros (l:list nat) : list nat :=
  match l with 
  | nil => nil
  | 0 :: l' => nonzeros l'
  | n :: l' => n :: (nonzeros l')
  end.

Fixpoint oddmembers (l:list nat) : list nat :=
  match l with 
  | nil => nil
  | n :: l' => 
    match (oddb n) with
    | true => n :: (oddmembers l')
    | false => oddmembers l'
    end
  end.

Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | n :: s' => match (eqb n v) with 
    | true => S (count v s')
    | false => count v s'
    end
  end.

Fixpoint remove_one (v:nat) (s:bag) : bag := 
  match s with
  | nil => nil
  | n :: s' => match (eqb v n) with
    | true => s'
    | false => n :: (remove_one v s')
    end
  end.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | n :: s' => match (eqb v n) with
    | true => remove_all v s'
    | false => n :: (remove_all v s')
    end
  end.

 *)

(* For exercises, these are functions from Poly.v. Again, 
   determine whether they can extended to cofixpoint or not. If not, 
   explain why. If can, extend it. You don't need to prove that your
   implementation is correct until now. *)

(*

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

 *)

(* So now, to reason on coinductive types and cofixpoint functions,
   we need dual of induction, so called coinduction. However, coq has
   no tactic called coinduction. Rather, we have one called cofix.
 *)

(* Before introducing Cofix, let's see what induction is. Simply, induction
   tactic is application of ***_ind theorem. However, how induction is proved
   is based on tactic called fix.
 *)

(* How fix work is exactly same as function fixpoint. Viewing proposition as
   a type, we obtain that induction is fixpoint construction. However,
   unlike induction where we only use direct subterms as IH, as fixpoint allows
   any subterms to be recurred, fix also allows it. In other words, induction
   is simplification of fix. Let's see very simple example with le.
 *)

Theorem le_trans :
  forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros. induction H0.
  - assumption.
  - apply le_S. apply IHle.
  Qed.

Theorem le_trans_fail :
  forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  fix IH 1. apply IH.
  (* Guarded. *)
  Abort.

Theorem le_trans' :
  forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros. generalize dependent n3.
  fix IH 2.
  intros. destruct H0.
  - assumption.
  - apply le_S. apply IH. apply H0.
  Qed.

(* So what happened here? We used fix to introduce duplicate
   of goal, and used it to prove our goal. However, as in
   le_trans_fail, direct application fails, since it is not
   correct induction. The constraint here, is that hypothesis
   generated with IH should be applied to subterm of goal.
   In le_trans' case, n1 <= n3 = le_S (n1 <= m), so application
   of IH on (n1 <= m) is ok. You will notice that this constraint
   is exactly same to fixpoint. *)

(* To check whether your proof satisfies constraint while proving, 
   you can use Guarded. This tactic checks current proof, and creates
   error if constraint is not satisfied, i.e. ill-formed recursion. *)

(* The number right after name of induction hypothesis is
   index of hypothesis that we will do induction on. Here, 
   our destruction is on n2 <= n3, so we used 2. One another requirement
   is that index we chosen should be inductively defined. 
   This is because since we can only perform induction on 
   inductive type/propositions. *)

(* There exist some theorems that are not easy to prove with 
   induction tactic, however possible with fix. One example is
   proving new induction principle for hereditarily finite sets. *)

Inductive hf : Set := HF (elts : list hf).

Check hf_ind.

Lemma hf_ind2 : forall P : hf -> Prop,
  (forall l, (forall x, In x l -> P x) -> P (HF l)) ->
  forall x, P x.
Proof.
  intros P Pnode.
  fix hf_ind 1.
  destruct x.
  apply Pnode.
  induction elts.
  - simpl. intros. elim H.
  - simpl. intros. destruct H.
    + elim H. apply hf_ind.
    + apply IHelts. assumption.
  Qed.

(* This lemma comes from 
   http://www.lix.polytechnique.fr/~barras/habilitation/v1/html/full/HF.html *)

(* Here, you will see elim tactic. Since fix is low level tactic
   unlike induction, constraint fails if we use rewrite, subst.
   So we use elim here, that makes coq to preserve constraint. *)

(* One of benefit using fix instead of induction is that, fix can give
   strong induction. In specific, you can apply induction hypothesis to
   any subterm of original one, so unlike induction tactic, which only allows
   direct subterm, we can perform strong induction. *)

(* Now, let's explain cofix. cofix is exactly same as fix, except
   we apply corecursion, not recursion. Constraint is similar to
   CoFixpoint, we should capsule on application of induction hypothesis. *)

(* Secondly, similar to requirement of fix, our goal should be coinductive.
   This is dual to requirement of fix, which required the argument to be
   inductive. So we need to have coinductive proposition. *)

CoInductive BiSimilarCL {X : Type} : CList X -> CList X -> Prop :=
| BiSim_cons (x : X) (cl1 cl2 : CList X) (H : BiSimilarCL cl1 cl2) : 
    BiSimilarCL (CCons x cl1) (CCons x cl2).

(* This definition gives alternative for equality on clist. For example, 
   we have that false :: true :: (alter false) = (alter false), however
   it is not provable in general. However, we can prove
   BiSimilar (false :: true :: (alter false)) (alter false). *)

(* But before proving, we have very useful lemma and definition. *)

Definition breakCL {X : Type} (l : CList X) := match l with
| CCons x l' => CCons x l'
end.

Lemma break_eqCL : forall {X : Type} (l : CList X), l = breakCL l.
Proof.
  intros. case l. simpl. reflexivity. Qed.

(* This definition is very trivial, however it is required when we
   wants to pattern match CList, in specific restart delayed computation. 
   If you use destruct, since destruct does not know on computation, 
   it just intros new variable, not exact value. *)

Theorem alter_same :
  BiSimilarCL (CCons false (CCons true (alter false))) (alter false).
Proof.
  cofix IH. 
  replace (alter false) with (CCons false (alter true)).
  replace (alter true) with (CCons true (alter false)).
  constructor. constructor. apply IH. Guarded.
  rewrite break_eqCL. simpl. reflexivity.
  rewrite break_eqCL. simpl. reflexivity.
  Qed.

(* You maybe tempting to add axiom that bisimilar induces equality, 

Axiom bisimilar_eq :
  forall {X : Type} (cl1 cl2 : CList X),
  BiSimilar cl1 cl2 -> cl1 = cl2.

   with assurance by following lemma. *)

Lemma bisimilar_prefix :
  forall {X : Type} (n : nat) (cl1 cl2 : CList X),
  BiSimilarCL cl1 cl2 -> prefix cl1 n = prefix cl2 n.
Proof.
  intros X n. induction n; intros.
  - simpl. reflexivity.
  - inversion H; subst. simpl.
    pose proof (IHn cl0 cl3 H0).
    rewrite H1. reflexivity.
  Qed.

(* The simple answer is, you don't need to. If some proposition is defined
   coinductively, you will be able to show that bisimilarity preserves that
   proposition using cofix. If not, that proposition is only able to reason
   on finite prefix of CList. This case bisimilar_prefix is enough. *)

(* Prove that Bisimilar is equivalence relation. *)

Lemma Bisimilar_refl :
  forall {X : Type} (cl : CList X),
  BiSimilarCL cl cl.
Proof.
  Admitted.

Lemma Bisimilar_symm :
  forall {X : Type} (cl1 cl2 : CList X),
  BiSimilarCL cl1 cl2 -> BiSimilarCL cl2 cl1.
Proof.
  Admitted.

Lemma Bisimilar_trans :
  forall {X : Type} (cl1 cl2 cl3 : CList X),
  BiSimilarCL cl1 cl2 -> BiSimilarCL cl2 cl3 -> BiSimilarCL cl1 cl3.
Proof.
  Admitted.

(* To be used to proof using coinductions, try to give some proof that
   analogous definition you defined to Lists.v and Poly.v are correct. *)

(* Countable List *)

(* Now we will see other CoList, this case we have exact same structure to
   that of list. *)

CoInductive CoList (X : Type) : Type :=
| CoNil : CoList X
| CoCons (x : X) (cl : CoList X) : CoList X.

(* What's going on here? It is very similar to CList, however we also allows
   finite list. In specific, CoList = CList + list. *)

(* This definition is well used when we are proving on possibly-terminating
   processes. The process may terminate(CoNil) or infinitely continue. Now we
   can define some proposition on finiteness. *)

Arguments CoCons {X} _ _.

Inductive FiniteCL {X : Type} : CoList X -> Prop :=
| FinNil : FiniteCL (CoNil X)
| FinCons (x : X) (cl : CoList X) (H : FiniteCL cl) : FiniteCL (CoCons x cl).

CoInductive InfiniteCL {X : Type} : CoList X -> Prop :=
| InfinCons (x : X) (cl : CoList X) (H : InfiniteCL cl) : InfiniteCL (CoCons x cl).

(* This is end of this section. Rest are problems that you maybe familiar to
   coinduction. *)

From Coq Require Import Omega.

(* Binary CoList is simple implementation of powerset of natural number.
   You will get good exercise in proving propositions I gave here. *)

CoInductive BiList : Type :=
| Yes (l : BiList) : BiList
| No (l : BiList) : BiList.

Definition break (l : BiList) := match l with
| Yes l' => Yes l'
| No l' => No l'
end.

Lemma break_eq : forall l, l = break l.
Proof.
  Admitted.

CoInductive BiSimilar : BiList -> BiList -> Prop :=
| BS_YesCons (l1 l2 : BiList) : BiSimilar l1 l2 -> BiSimilar (Yes l1) (Yes l2)
| BS_NoCons (l1 l2 : BiList) : BiSimilar l1 l2 -> BiSimilar (No l1) (No l2).

CoInductive AllTrue : BiList -> Prop :=
| YesCons (l : BiList) : AllTrue l -> AllTrue (Yes l).

CoFixpoint TTT : BiList := Yes TTT.

Example TTTTrue : AllTrue TTT.
Proof.
  Admitted.

Example TrueTTT : forall l, AllTrue l -> BiSimilar l TTT.
Proof.
  Admitted.

CoInductive AllFalse : BiList -> Prop :=
| NoCons (l : BiList) : AllFalse l -> AllFalse (No l).

CoFixpoint FFF : BiList := No FFF.

Example FFFFalse : AllFalse FFF.
Proof.
  Admitted.

Example FalseFFF : forall l, AllFalse l -> BiSimilar l FFF.
Proof.
  Admitted.

Inductive AllButFinitelyMany : BiList -> Prop := .

Inductive FinitelyMany : BiList -> Prop := .

Definition InfinitelyMany (l : BiList) := ~ (FinitelyMany l).

CoFixpoint alterbool (b : bool) := match b with
| true => Yes (alterbool false)
| false => No (alterbool true)
end.

Example alter_infinite :
  forall b, (b = alterbool true \/ b = alterbool false) -> InfinitelyMany b.
Proof.
  Admitted.

Lemma AT_ABFM :
  forall l, AllTrue l -> AllButFinitelyMany l.
Proof.
  Admitted.

Lemma AT_IM :
  forall l, AllTrue l -> InfinitelyMany l.
Proof.
  Admitted.

Lemma ABFM_IM :
  forall l, AllButFinitelyMany l -> InfinitelyMany l.
Proof.
  Admitted.

CoFixpoint fromFunAux (f : nat -> bool) (n : nat) :=
  if (f n) then Yes (fromFunAux f (S n)) else No (fromFunAux f (S n)).

Definition fromFun (f : nat -> bool) := fromFunAux f 0.

(*
 *  Note that 
 *  AllFalse -> Finite
 *  AllTrue -> AllButFinitelyMany -> Infinite
 *  State some example that
 *  1. Finite, not AllFalse
 *  2. AllButFinitelyMany, not AllTrue
 *  3. Infinite, not AllButFinitelyMany
 *)

Fixpoint count (l : BiList) (n : nat) :=
  match n with
  | 0 => 0
  | S n' =>
    match l with
    | Yes l' => S (count l' n')
    | No l' => count l' n'
    end
  end.

Definition countFinite (l : BiList) :=
  exists n, forall n', n' > n -> count l n' = count l n.

Definition countInfinite (l : BiList) :=
  forall c, exists n, count l n > c.

Definition countAllFalse (l : BiList) :=
  forall n, count l n = 0.

Definition countAllTrue (l : BiList) :=
  forall n, count l n = n.

Theorem countAllTrueCorrect :
  forall l, countAllTrue l <-> AllTrue l.
Proof.
  Admitted.

Theorem countAllFalseCorrect :
  forall l, countAllFalse l <-> AllFalse l.
Proof.
  Admitted.

Theorem countFiniteCorrect :
  forall l, countFinite l <-> FinitelyMany l.
Proof.
  Admitted.

Theorem countInfiniteCorrect :
  forall l, countInfinite l -> InfinitelyMany l.
Proof.
  Admitted.

(* You can not prove 

Theorem countInfiniteCorrect2 :
  forall l, InfinitelyMany l -> countInfinite l.

   Can you explain why?
 *)

Theorem countInfiniteNotFinite :
  forall l, countInfinite l -> countFinite l -> False.
Proof.
  Admitted.

(* This is end of exercise. There are lots of good exercise
   problems on coinduction with coq, so I recommend trying them also.
   For more practical examples, I recommend my currently ongoing
   project.
   https://github.com/mekty2012/Theories-of-Programming-Languages-Implementation/blob/master/Domain.v
   Here, around definition of DLle, you can see some techniques proving 
   coinductive definition by introducing induction principle.
   *)





