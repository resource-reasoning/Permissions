Require Import SetoidClass Morphisms.

Module Type ShallowPermissionTheory.
  (* Type of a model of a permission theory *)

  Parameter perm : Type.
  Declare Instance perm_Setoid : Setoid perm.

  (* composition of permissions *)
  Parameter C : perm -> perm -> perm -> Prop.
  Declare Instance C_morphism : Proper (equiv ==> equiv ==> equiv ==> iff) C.

  Parameter full : perm.
  Parameter empty : perm.

  Axiom C_commutative : forall p p' p'', C p p' p'' -> C p' p p''.

  Axiom C_full_empty : forall p p', C full p p' -> p == empty.
  Axiom C_full_full : forall p p', C full p p' -> p' == full.

  Axiom C_non_idempotent : forall p p', C p p p' -> p == empty.

  Axiom C_identity : forall p, C empty p p.

  Axiom C_functional : forall p p' p'' p''', C p p' p'' -> C p p' p'' -> p'' == p'''.

  Axiom C_inverse : forall p, exists p', C p p' full.

  Axiom C_associative : forall p1 p2 p3 p,
     (exists p12, C p1 p2 p12 /\ C p12 p3 p) <->
     (exists p23, C p2 p3 p23 /\ C p1 p23 p).

  Axiom C_divisibility : forall p, p == empty \/
    exists p1, exists p2, ~(p1 == empty) /\ ~(p2 == empty) /\ C p1 p2 p.

  Axiom non_trivial : ~ (full == empty).
  Axiom equiv_dec : forall p p' : perm, p == p' \/ ~ p == p'.
  Axiom C_dec : forall p p' p'' : perm, C p p' p'' \/ ~ C p p' p''.

End ShallowPermissionTheory.

Module ShallowPermissionProperties (Import SPT : ShallowPermissionTheory).
  Definition O : perm -> perm -> Prop := fun p1 p2 => forall p, ~ C p1 p2 p.

  Hint Unfold O.

  Lemma overlap_or_empty : forall p, O p p \/ p == empty.
   unfold O; intro.
   destruct (equiv_dec p empty); firstorder.
   left.
   intro; contradict H.
   eapply C_non_idempotent; eauto.
  Qed.


End ShallowPermissionProperties.

Section DeepPermissions.

  Inductive dpf :=
    | dpf_false : dpf
    | dpf_and : dpf -> dpf -> dpf
    | dpf_or : dpf -> dpf -> dpf
    | dpf_not : dpf -> dpf
    | dpf_eq : nat -> nat -> dpf
    | dpf_C : nat -> nat -> nat -> dpf
    | dpf_all : dpf -> dpf
    | dpf_ex : dpf -> dpf.

  Inductive eval_tree :=
    | some : eval_tree
    | none : eval_tree
    | branch : eval_tree.

End DeepPermissions.

Set Implicit Arguments.

Require Import List Eqdep_dec.

Definition llist A n := {l : list A | length l = n}.

Lemma ll_proj_eq A n : forall (l l' : llist A n), proj1_sig l = proj1_sig l' -> l = l'.
 intros.
 destruct l.
 destruct l'.
 simpl in H.
 subst.
 f_equal.
 apply eq_proofs_unicity.
 decide equality.
Defined.

  Import Plus.


Program Definition llrev A n (l : llist A n) : llist A n := 
  rev l.
Obligation 1.
 destruct l.
 revert n e.
 induction x; intros.
  simpl in *; subst; reflexivity.
  simpl in *; subst.
  rewrite app_length.
  simpl.
  rewrite (IHx (length x)) by reflexivity.
  rewrite <- plus_Snm_nSm.
  rewrite plus_0_r.
  reflexivity.
Qed.

Program Definition llcons A n (x : A) (xs : llist A n) : llist A (S n) := cons x xs.
Obligation 1.
 destruct xs; subst.
 reflexivity.
Qed.

Program Definition llnil A : llist A 0 := nil.

Program Definition llhead A n (l : llist A (S n)) : A :=
  match l with
  | nil => _
  | cons x xs => x
  end.
Obligation 1.
 destruct l.
 simpl in *.
 subst; inversion e.
Qed.

Program Definition lltail A n (l : llist A (S n)) : llist A n :=
  match l with
  | nil => _
  | cons x xs => xs
  end.
Obligation 1.
 destruct l; simpl in *; subst.
 inversion e.
Qed.
Obligation 2.
  revert l x xs Heq_l.
  induction n; intuition;
   destruct l; simpl in *; subst;
   inversion e; reflexivity.
Qed.

Program Definition llsnoc A n (l : llist A n) a : llist A (S n) :=
  l ++ (a :: nil).
Obligation 1.
 rewrite app_length.
 rewrite plus_comm.
 destruct l.
 subst; reflexivity.
Qed.

Program Fixpoint llcohead A n (l : llist A (S n)) : A :=
  match l with
  | nil => _
  | cons x xs => match n with
     | O => x
     | S m => llcohead (n:=m) xs end
  end.
Obligation 1.
 destruct l; simpl in *; subst.
 inversion e.
Qed.
Obligation 2.
 destruct l; simpl in *; subst.
 inversion e; auto.
Qed.


Program Fixpoint llcotail A n (l : llist A (S n)) : llist A n :=
  match l with
  | nil => _
  | cons x xs => match n with
    | O => nil
    | S m => cons x (llcotail (n:=m) xs) end
  end.
Next Obligation.
 destruct l; simpl in *; subst.
 inversion e.
Qed.
Next Obligation.
 destruct l; simpl in *; subst.
 inversion e; auto.
Qed.


 


  Hint Resolve ll_proj_eq.
  Lemma llist_head_tail A n (l : llist A (S n)) : llcons (llhead l) (lltail l) = l.
   destruct l.
   destruct x.
    inversion e.
    auto with *.
  Defined.

  Hint Resolve llist_head_tail.

  Lemma llist_ind A : forall P : (forall n, llist A n -> Type),
    P O (llnil A) ->
    (forall n l, P n l -> forall a, P (S n) (llcons a l)) ->
    (forall n l, P n l).
   intros.
   induction n.
    destruct l.
    destruct x; subst.
     match goal with |- P 0 ?x => replace x with (llnil A); auto end.
     inversion e.
   
    replace l with (llcons (llhead l) (lltail l)); auto.
  Defined.    

  Lemma llist_ind0 A : forall P : (llist A 0 -> Type),
    P (llnil A) -> (forall l, P l).
   intros.
   destruct l.
    destruct x; subst.
     match goal with |- P ?K => replace K with (llnil A); auto end.
     inversion e.
  Defined.

  Lemma llist_indS A : forall P : (forall n, llist A (S n) -> Type),
    (forall a,  P O (llcons a (llnil A))) ->
    (forall n l, P n l -> forall a, P (S n) (llcons a l)) ->
    (forall n l, P n l).
   intros.
   induction n.
    destruct l.
    destruct x; subst.
     inversion e.
     match goal with |- P 0 ?x => replace x with (llcons a (llnil A)); auto end.
     inversion e.
      destruct x.
       auto.
       inversion H0.
   
    replace l with (llcons (llhead l) (lltail l)); auto.
  Defined.

  Lemma llist_cotail A n a (l : llist A (S n)) :
      llcotail (llcons a l) = llcons a (llcotail l).
   revert a.
   revert n l.
   refine (llist_indS (fun l => _) _ _); intros.
    auto.
    rewrite H.
    apply ll_proj_eq.
    simpl.
    repeat f_equal.
    apply ll_proj_eq; auto.
  Qed.

  Lemma llist_cohead A n a (l : llist A (S n)) :
      llcohead (llcons a l) = llcohead l.
   destruct l.
   simpl.
   f_equal.
   apply ll_proj_eq.
   reflexivity.
  Qed.

  Lemma llist_snoc_cons A n a b (l : llist A n) :
     llsnoc (llcons a l) b = llcons a (llsnoc l b).
   revert a b.
   induction l using llist_ind; intros.
    auto.
    auto.
  Qed.

  Lemma llist_cohead_cotail A n (l : llist A (S n)) :
     llsnoc (llcotail l) (llcohead l) = l.
   revert n l;
   refine (llist_indS (fun l => _) _ _); intros.
    auto.
    rewrite llist_cotail.
    rewrite llist_snoc_cons.
    f_equal.
    auto.
    rewrite llist_cohead.
    trivial.
  Qed.

Lemma llist_snoc_ind A : forall P : (forall n, llist A n -> Type),
    P O (llnil A) ->
    (forall n l, P n l -> forall a, P (S n) (llsnoc l a)) ->
    (forall n l, P n l).
 intros.
 induction n.
  destruct l.
  destruct x; subst.
   match goal with |- P 0 ?x => replace x with (llnil A); auto end.
   inversion e.

  rewrite <- llist_cohead_cotail.
  firstorder.
Qed.


Ltac llniltac := 
 match goal with L : llist _ 0 |- _ => revert L; refine (llist_ind0 (fun L => _) _) end.



Lemma ll_snoc_rev_cons A n (l : llist A n) a : llcons a (llrev l) = llrev (llsnoc l a).
 revert a.
 induction l using llist_ind.
  auto.

  intros.

  apply ll_proj_eq.
  simpl.
  rewrite app_comm_cons.
  f_equal.
  generalize (IHl a0); intro.
  inversion H.
  firstorder.
Qed.
 


(*

Program Definition myl : llist nat 2 := 1 :: 2 :: nil.

Compute (llsnoc myl 7).

Compute (llhead (lltail myl)).

Compute (proj1_sig (llrev myl)).
*)

(*
Set Contextual Implicit Arguments.




Inductive vector (A : Type) : nat -> Type :=
  | vnil : vector A 0
  | vcons : forall n, A -> vector A n -> vector A (S n)
.


Definition vrev A n (xs : vector A n) : forall m, vector A m -> vector A (n+m).
induction xs; intros.
 exact X.
 replace (S n + m) with (n + S m).
 apply IHxs.
 exact (vcons a X).
 clear; induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Defined.
(*
Program Fixpoint vrev A n (xs : vector A n) : forall m, vector A m -> vector A (n+m) :=
  fun m =>
  match xs in vector _ i return vector A m -> vector A (i+m) with
  | vnil => (fun (rs : vector A m) => rs)
  | vcons i x xs' => fun rs => vrev xs' (vcons x rs)
  end.
*)

Definition vreverse {A} n (xs : vector A n) : vector A n.
  replace n with (n + 0).
  exact (vrev xs (vnil A)).
  clear; induction n; try reflexivity.
   simpl; rewrite IHn; reflexivity.
Defined.

(*
Program Definition vreverse {A} n (xs : vector A n) : vector A n := vrev xs (@vnil A).
Compute (vreverse (vcons true (vcons false (vnil bool)))).
*)

Fixpoint vtol0 A n (v : vector A n) : list A :=
  match v with
  | vnil => nil
  | vcons m x xs => cons x (vtol0 xs)
  end.

Lemma vtol0_length A n (v : vector A n) : length (vtol0 v) = n.
 induction v; auto.
 simpl.
 f_equal.
 trivial.
Defined.

Definition vtol A n (v : vector A n) : {l : list A | length l = n} :=
  exist _ _ (vtol0_length v).

(*
Program Fixpoint vtol A n (v : vector A n) : {l : list A & length l = n} :=
  match v with
  | vnil => @existT _ _ nil _
  | vcons m x xs => let (a, b) := vtol xs in @existT  _ _ (cons x a) _
  end.
*)

Definition ltov A n (l : {l : list A | length l = n}) : vector A n.
 induction n.
  apply vnil.
  destruct l.
  destruct x.
   inversion e.
   apply vcons.
   exact a.
   apply IHn.
   simpl in e.
   exists x.
   injection e; trivial.
Defined.

Require Import Eqdep_dec.

 

Lemma ltov_vtol A n (v : vector A n) : ltov (vtol v) = v.
 induction v.
  reflexivity.
  simpl.
  f_equal.
  rewrite <- IHv at 8.
  unfold vtol.
  f_equal.
  f_equal.
  apply eq_proofs_unicity.
  decide equality.
Qed.

Lemma length_list_equal A n (l1 l2 : {l : list A | length l = n}) :
  (let (l1l, _) := l1 in let (l2l, _) := l2 in l1l = l2l) -> l1 = l2.
intro.
destruct l1.
destruct l2.
subst.
f_equal.
apply eq_proofs_unicity.
decide equality.
Qed.

Lemma vtol_ltov A n (l : {l : list A | length l = n}) : vtol (ltov l) = l.
 induction n.
  destruct l.
  destruct x.
   simpl.
   unfold vtol.
   f_equal.
   apply eq_proofs_unicity; decide equality.

   inversion e.

  destruct l.
  destruct x.
   inversion e.
   inversion e.
   unfold vtol.
   apply length_list_equal.
   generalize (IHn (exist _ _ H0)); intro.
   inversion H.
   simpl; f_equal.
   rewrite <- H2 at 3.
   f_equal.
   f_equal.
   f_equal.
   apply eq_proofs_unicity.
   decide equality.
Qed.

Require Import List.

Definition llrev A n (l : {l : list A | length l = n}) : {l : list A | length l = n}

(*
Compute (vtol (vcons 1 (vnil _) )). *)
*)

Module InhabitationFunctionDefs.
  Open Scope bool.
  Definition inhf n := llist bool n -> bool.
  Definition restrict n (f : inhf (S n)) : inhf n :=
    fun v => f (llcons true v) || f (llcons false v).
  Program Instance inhf_setoid n : Setoid (inhf n) :=
    {| equiv := fun f g => forall v, f v = g v |}.
  Obligation 1.
   split; try firstorder.
   repeat intro.
   rewrite H; firstorder.
  Qed.

  Definition is_extension_of n (f : inhf (S n)) (g : inhf n) := restrict f == g.

  Definition empty_inhf : inhf 0 := fun _ => true.
  
End InhabitationFunctionDefs.


Module Type InhabitationGrid.
  Import InhabitationFunctionDefs.
  Parameter grid : nat -> Type.
  Parameter eval : forall n, grid n -> llist bool n -> bool.
  Parameter empty_grid : grid 0.
  Parameter extensions : forall n, grid n -> list (grid (S n)).
  Axiom empty_grid_is_empty : forall v, eval empty_grid v = true.
  Axiom extensions_are_extensions : forall n (f : grid (S n)) (g : grid n),
    In f (extensions g) -> is_extension_of (eval f) (eval g).
  Axiom all_extensions : forall n (g : grid n) (f' : inhf (S n)), 
    is_extension_of f' (eval g) -> exists f,
      In f (extensions g) /\ f' == eval f.
End InhabitationGrid.

Fixpoint mix_with {A B C} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
  match la with
  | nil => nil
  | cons x xs => (map (f x) lb) ++ mix_with f xs lb
  end.

Lemma In_mix_with {A B C} (f : A -> B -> C) la lb :
  forall z, In z (mix_with f la lb) <-> exists x, exists y, In x la /\ In y lb /\ z = f x y.
 induction la.
  simpl; firstorder.
  simpl; intuition.
   apply in_app_or in H; destruct H.
    clear IHla.
    induction lb.
     contradiction H.
     destruct H.
      subst; exists a; exists a0; intuition.
      apply IHlb in H; destruct H; destruct H.
      intuition; subst.
       exists x; exists x0; intuition.
       exists x; exists x0; intuition.
   firstorder.

   firstorder; subst.
   remember lb as lb'.
   rewrite Heqlb' at 2; clear Heqlb'.
   clear IHla; induction lb'.
    contradiction H0.
    firstorder; subst.
     left; reflexivity.
Qed.


Module TreeInhabitationGrid.
  Import InhabitationFunctionDefs.
  Inductive et : nat -> Type :=
    | et_some : et 0
    | et_none : forall n, et n
    | et_branch : forall n, et n -> et n -> et (S n).
(*
  Inductive inhabited : forall n, et n -> Prop :=
    | eti_some : inhabited et_some
    | eti_branch_l : forall n (x x': et n), inhabited x -> inhabited (et_branch x x')
    | eti_branch_r : forall n (x x': et n), inhabited x' -> inhabited (et_branch x x').

  Definition grid n := {x : et n | inhabited x}.
*)

  Definition grid := et.

  Program Fixpoint eval' n (g : grid n) (l : llist bool n) : bool :=
    match g with
    | et_some => true
    | et_none m => false
    | et_branch m L R => match l with
      | nil => _
      | cons b bs => if b then eval' R bs else eval' L bs end
    end.
  Obligation 1.
   destruct l.
   simpl in Heq_l; subst.
   inversion e.
  Qed.
  Obligation 2.
   destruct l.
   simpl in *; subst.
   inversion e; auto.
  Qed.
  Obligation 3.
   destruct l.
   simpl in *; subst.
   inversion e; auto.
  Qed.

(*
  Definition eval' : forall n, grid n -> llist bool n -> bool.
   fix 1.
   intro.
   destruct n; intros g v.
    inversion g.
     exact true.
     exact false.
    inversion g.
     exact false.
     exact (match llhead v with
         | false => eval' n H0 (lltail v)
         | true => eval' n H1 (lltail v) end).
  Defined. *)
  Definition eval n (g : grid n) (v : llist bool n) :=
    eval' g (llrev v).

(*
  Compute (eval (et_branch et_some (et_none 0)) (llcons true (llnil bool))).
  Compute (eval (et_branch (et_branch et_some (et_some)) (et_none 1)) (llcons true (llcons false (llnil bool)))).
*)

  Definition empty_grid := et_some.
  Proposition empty_grid_is_empty : forall v, eval empty_grid v = true.
   firstorder.
  Qed.


  Fixpoint extensions n (g : grid n) : list (grid (S n)) :=
  match g with
  | et_some => et_branch et_some et_some :: et_branch et_some (et_none 0) :: et_branch (et_none 0) et_some :: nil
  | et_none m => et_none (S m) :: nil
  | et_branch m l r => mix_with (@et_branch (S m) ) (extensions l) (extensions r)
  end.

(*  Compute (extensions (et_branch (et_branch et_some et_some) (et_branch (et_none _) (et_some)))). *)
  
  Lemma eval_branch n (g1 g2 : grid n) v : eval' (et_branch g1 g1) (llcons true v) = eval' g1 v.
   simpl.
   f_equal.
   apply ll_proj_eq.
   reflexivity.
  Qed.


  Proposition extensions_are_extensions : forall n (f : grid (S n)) (g : grid n),
    In f (extensions g) -> is_extension_of (eval f) (eval g).
   induction n.
    intros.
    destruct g; simpl in H; intuition; subst;
     intro v; try (refine (llist_ind0 (fun v => _) _ v)); try reflexivity.
     
     intro v.
     reflexivity.
     
    inversion f.
   induction f; intros.

(* *)


   induction g; intros.
    simpl in H; intuition; subst; intro;
     refine (llist_ind0 (fun v => _) _ v);
     reflexivity.
    simpl in H; intuition; subst; intro.
     induction v using llist_ind; auto with *.

    simpl in H.
     apply In_mix_with in H.
     destruct H; destruct H; intuition; subst.
     apply IHg1 in H0.
     apply IHg2 in H.
     intro.
     clear -H0 H.


     unfold eval in *.
     unfold is_extension_of in *.
     unfold restrict in *.
     replace (llrev v) with (llcons (llhead (llrev v)) (lltail (llrev v))) by auto.
     simpl.

     unfold eval' at 3.
     2: apply llist_head_tail.
     generalize (H0 (lltail v)); intro.
     simpl in H1.
     induction v using llist_ind.
     simpl.
     unfold eval' at 1.
     unfold
  
     simpl. 

     reflexivity.
     reflexivity.





(* *)
    simpl in H; intuition; subst; intro;
     refine (match v in (vector _ n) with vnil => _ | vcons _ _ _ => id end);
     reflexivity.

    simpl in H; intuition; subst.
     intro.
     induction v.
      reflexivity.
      reflexivity.

   simpl in H.
   apply In_mix_with in H.
   destruct H; destruct H; intuition; subst.
   apply IHg1 in H0.
   apply IHg2 in H.
   intro.
   clear -H0 H.

   unfold is_extension_of in H0.
   unfold eval in *.
   unfold equiv in H0.
   unfold inhf_setoid in H0.
   set (H0 v).
   simpl in H0.
   simpl.
   generalize (vreverse v).

   unfold eval.

   

   refine (match v in (vector _ n0) with vnil => id | _ => _ end).
   
   inversion v.

    refine 


   induction n.
    
    refine (match v in (vector _ n) with vnil => id | vcons _ _ _ => _ end).


   refine (match v with vnil => _ | vcons _ _ _ => _ end _).
   unfold eval.
   unfold eval'.
   simpl.
   refine (match v in (vector _ m) with vnil => id | vcons _ _ _ => _ end).

   induction (extensions g1).
    contradiction H.

     reflexivity.


      ID
     refine (match v with _ => _ end).
     set (n := 0).
     destruct v.
     change (vector bool n) in v.
     assert (n = 0) by reflexivity.
     revert n v H.
     induction v.
     intro.
    subst.

    induc
   inversion H.
   induction H.
   intros.
   simpl in H.

  Axiom all_extensions : forall n (g : grid n) (f' : inhf (S n)), 
    is_extension_of f' (eval g) -> exists f,
      In f (extensions g) /\ f' == eval f.


Module Type InhabitationGridSpec (Import ig : InhabitationGrid).
  Axiom eval_empty_true : forall v, eval empty_grid v = true.
  Axiom eval_
  
  

