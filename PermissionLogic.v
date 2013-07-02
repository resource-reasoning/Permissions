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

Module InhabitationFunctionDefs.
  Open Scope bool.
  Definition inhf n := vector bool n -> bool.
  Definition restrict n (f : inhf (S n)) : inhf n :=
    fun v => f (vcons true v) || f (vcons false v).
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

Require Import List.


Module Type InhabitationGrid.
  Import InhabitationFunctionDefs.
  Parameter grid : nat -> Type.
  Parameter eval : forall n, grid n -> vector bool n -> bool.
  Parameter empty_grid : grid 0.
  Parameter extensions : forall n, grid n -> list (grid (S n)).
  Axiom empty_grid_is_empty : forall v, eval empty_grid v = true.
  Axiom extensions_are_extensions : forall n (f : grid (S n)) (g : grid n),
    In f (extensions g) -> is_extension_of (eval f) (eval g).
  Axiom all_extensions : forall n (g : grid n) (f' : inhf (S n)), 
    is_extension_of f' (eval g) -> exists f,
      In f (extensions g) /\ f' == eval f.
End InhabitationGrid.

Module TreeInhabitationGrid.
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
  Definition eval' : forall n, grid n -> vector bool n -> bool.
   fix 1.
   intro.
   destruct n; intros g v.
    inversion g.
     exact true.
     exact false.
    inversion g.
     exact false.
     inversion v.
     exact (match H3 with false => eval' n H0 H4 | true => eval' n H1 H4 end).
  Defined.
  Definition eval n (g : grid n) (v : vector bool n) :=
    eval' g (vreverse v).
  Definition empty_grid := et_some.
  


Module Type InhabitationGridSpec (Import ig : InhabitationGrid).
  Axiom eval_empty_true : forall v, eval empty_grid v = true.
  Axiom eval_
  
  

