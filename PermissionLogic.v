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

Set Implicit Arguments.


Section DeepPermissions.

  Inductive dpf : nat -> Set :=
    | dpf_false : forall n, dpf n
    | dpf_and : forall n, dpf n -> dpf n -> dpf n
    | dpf_or : forall n, dpf n -> dpf n -> dpf n
    | dpf_not : forall n, dpf n -> dpf n
    | dpf_eq : forall n, forall n0, n > n0 -> forall n1, n > n1 -> dpf n
    | dpf_C : forall n, forall n0, n > n0 -> forall n1, n > n1 -> forall n2, n > n2 -> dpf n
    | dpf_all : forall n, dpf (S n) -> dpf n
    | dpf_ex : forall n, dpf (S n) -> dpf n.

End DeepPermissions.

Require Import LList.
Require Import List.


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

Section DeepPermissionsSatisfaction.
  Import InhabitationFunctionDefs.
(*
  Program Fixpoint dpf_empty_inter2 n (v1 : nat) (c1 : bool)
          (v2 : nat) (c2 : bool) (i : inhf n) : bool :=
   |
*)
  Inductive dpf_empty_inter2 : forall n, (nat * bool) -> (nat * bool) -> inhf n -> Prop :=
   | .

  Inductive dpf_sat : forall n, dpf n -> inhf n -> Prop :=
  | dpfs_and : forall n (l : dpf n)  r i, dpf_sat l i -> dpf_sat r i -> dpf_sat (dpf_and l r) i
  | dpfs_orl : forall n (l : dpf n) r i, dpf_sat l i -> dpf_sat (dpf_or l r) i
  | dpfs_orr : forall n (l : dpf n) r i, dpf_sat r i -> dpf_sat (dpf_or l r) i
  | dpfs_not : forall n (f : dpf n) i, dpf_unsat f i -> dpf_sat (dpf_not f) i
  with dpf_unsat : forall n, dpf n -> inhf n -> Prop :=
  | dpfu_false : forall n i, dpf_unsat (dpf_false n) i
  | dpfu_andl : forall n (l : dpf n) r i, dpf_unsat l i -> dpf_unsat (dpf_and l r) i
  | dpfu_andr : forall n (l : dpf n) r i, dpf_unsat l i -> dpf_unsat (dpf_and l r) i
  | dpfu_or : forall n (l : dpf n) r i, dpf_unsat l i -> dpf_unsat r i -> dpf_unsat (dpf_or l r) i
  | dpfu_not : forall n (f : dpf n) i, dpf_sat f i -> dpf_unsat (dpf_not f) i
  .

(*
  Variable dpf_prop : dpf 0 -> Prop.
  Variable dpf_prov : forall (f : dpf 0), dpf_sat f (fun _ => true) -> dpf_prop f.
  Variable dpf_nprov : forall (f : dpf 0), dpf_unsat f (fun _ => true) -> ~dpf_prop f.
  Variable dpf_dec : forall (f : dpf 0), dpf_sat f (fun _ => true) \/ dpf_unsat f (fun _ => true).
  Lemma dpf_prop_prov : forall f, dpf_prop f -> dpf_sat f (fun _ => true).
  firstorder.
  Qed.
*)
  




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


  Lemma eval'_branch n (g1 g2 : grid n) b v : eval' (et_branch g1 g2) (llcons b v) = if b then eval' g2 v else eval' g1 v.
   simpl.
   destruct b;
   f_equal;
   apply ll_proj_eq;
   auto.
  Qed.


  Lemma extension_foo : forall n (f : grid (S n)) (g : grid n),
    In f (extensions g) -> forall v, eval' g v = eval' f (llsnoc v true) || eval' f (llsnoc v false).
   induction g; intros.
    simpl in *.
    llniltac; intuition; subst; auto.

    simpl in *; intuition.
    subst; auto.

    simpl in H.
    apply In_mix_with in H.
    destruct H; destruct H; intuition; subst.
    generalize (IHg1 _ H0 (lltail v)); intro.
    generalize (IHg2 _ H (lltail v)); intro.
    clear IHg1 IHg2 H H0.
    replace v with (llcons (llhead v) (lltail v)) in * by auto.
    rewrite llist_tail_cons in *.
    rewrite eval'_branch.
    rewrite H1, H2.
    rewrite llist_snoc_cons.
    rewrite llist_snoc_cons.
    do 2 rewrite eval'_branch.
    destruct (llhead v); auto.
  Qed.
  Hint Resolve extension_foo.

  Proposition extensions_are_extensions : forall n (f : grid (S n)) (g : grid n),
    In f (extensions g) -> is_extension_of (eval f) (eval g).
   intros.
   intro.
   unfold restrict.
   unfold eval.
   do 2 rewrite ll_cons_rev_snoc.
   symmetry; auto.
  Qed.




  Proposition all_extensions : forall n (g : grid n) (f' : inhf (S n)), 
    is_extension_of f' (eval g) -> exists f,
      In f (extensions g) /\ f' == eval f.
   induction g; intuition.
    unfold is_extension_of in H.
    generalize (H (llnil bool)); intro e.
    unfold restrict in e.
    remember (f' (llcons false (llnil _))) as b1.
    remember (f' (llcons true (llnil _))) as b2.
    cbv -[orb] in e.
    exists (et_branch (if b1 then et_some else et_none 0)
               (if b2 then et_some else et_none 0)).
     destruct b1; destruct b2;
     simpl; intuition;
    revert v; apply llist_ind1; intro;
    destruct a; (rewrite <- Heqb1 || rewrite <- Heqb2); auto.

    exists (et_none (S n)).
    simpl; intuition.
    generalize (H (lltail v)); intro.
    unfold restrict in H0.
    cbv -[orb llcons lltail] in H0.
    cbv.
    replace v with (llcons (llhead v) (lltail v)) by auto.
    destruct (llhead v);
     match goal with |- ?F = false => destruct F; auto; inversion H0 end.
    match goal with |- _ = ?F || _ => destruct F; auto end.

    unfold is_extension_of in *.
    set (f1 := (fun l => f' (llsnoc l false)) : inhf (S n) ).
    set (f2 := (fun l => f' (llsnoc l true)) : inhf (S n) ).
    simpl in H.
     assert (restrict f1 == eval g1).
      intro.
      unfold f1.
      unfold restrict in *.
      do 2 rewrite llist_snoc_cons.
      rewrite H.
      unfold eval.
      rewrite <- ll_snoc_rev_cons.
      simpl; f_equal.
      apply ll_proj_eq; auto.
     assert (restrict f2 == eval g2).
      intro.
      unfold f2.
      unfold restrict in *.
      do 2 rewrite llist_snoc_cons.
      rewrite H.
      unfold eval.
      rewrite <- ll_snoc_rev_cons.
      simpl; f_equal.
      apply ll_proj_eq; auto.
     apply IHg1 in H0.
     apply IHg2 in H1.
     destruct H0; destruct H1; intuition.
     exists (et_branch x x0).
     split.
      simpl.
      apply In_mix_with.
      firstorder.

      intro.
      unfold eval.
      replace (llrev v) with (llcons (llhead (llrev v)) (lltail (llrev v))) by auto.

      rewrite llhead_cohead.
      rewrite <- (llist_cohead_cotail) at 1.
      rewrite eval'_branch.
      destruct (llcohead v).
       replace (f' (llsnoc (llcotail v) true)) with (f2 (llcotail v)) by auto.
       rewrite H4.
       unfold eval; f_equal; auto.

       replace (f' (llsnoc (llcotail v) false)) with (f1 (llcotail v)) by auto.
       rewrite H3.
       unfold eval; f_equal; auto.
  Qed.

End TreeInhabitationGrid.
