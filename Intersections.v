Require Import SetoidClass.
Set Implicit Arguments.

Module Type ShallowIntersectionTheory.

  (* The type of permissions, the only sort in the theory *)
  Parameter perm : Type.

  (* Equivalence on permissions *)
  Declare Instance perm_setoid : Setoid perm.

  (* Intersection relation on permissions *)
  Parameter inter : perm -> perm -> perm -> Prop.
  
  Declare Instance inter_respectful : Proper (equiv ==> equiv ==> equiv ==> iff) inter.
  Axiom ax_inter_total : forall a b, exists ab, inter a b ab.
  Axiom ax_inter_functional : forall a b ab1 ab2, inter a b ab1 -> inter a b ab2 -> ab1 == ab2.
  Axiom ax_inter_symmetric : forall a b ab, inter a b ab -> inter b a ab.
  Axiom ax_inter_self : forall a, inter a a a.
  Axiom ax_inter_associative : forall a b c ab abc, inter a b ab -> inter ab c abc ->
          forall bc, inter b c bc -> inter a bc abc.
  Axiom ax_inter_decidable : forall a b c, inter a b c \/ ~ inter a b c.

  Parameter empty : perm -> Prop.
  Declare Instance empty_respectful : Proper (equiv ==> iff) empty.
  Axiom ax_empty_unique : forall a, empty a -> forall b, empty b -> a == b.
  Axiom ax_empty_exists : exists a, empty a.
  Axiom ax_empty_notall : exists a, ~ empty a.
  Axiom ax_empty_decidable : forall a, empty a \/ ~ empty a.

  Axiom ax_empty_inter : forall a b, empty a -> inter a b a.

  Parameter compl : perm -> perm -> Prop.
  Declare Instance compl_respectful : Proper (equiv ==> equiv ==> iff) compl.
  Axiom ax_compl_total : forall a, exists b, compl a b.
  Axiom ax_compl_functional : forall a b1 b2, compl a b1 -> compl a b2 -> b1 == b2.
  Axiom ax_compl_symmetric : forall a b, compl a b -> compl b a.
  Axiom ax_compl_irreflexive : forall a, ~ compl a a.
  Axiom ax_compl_decidable : forall a b, compl a b \/ ~ compl a b.

  Axiom ax_compl_inter_empty : forall a b, compl a b -> forall c, inter a b c -> empty c.
  Axiom ax_compl_empty_inter : forall a a', empty a -> compl a a' -> forall b, inter a' b b.
  Axiom ax_division : forall a, empty a \/ exists b, 
                                  (forall ab, inter a b ab -> ~ empty ab) /\
                                  (forall b' ab', compl b b' -> inter a b' ab' -> ~ empty ab').


  Axiom ax_inter_equiv : forall a b a' b', compl a a' -> compl b b' ->
     (forall x, inter a b' x -> empty x) ->
       (forall x, inter a' b x -> empty x) -> a == b.


End ShallowIntersectionTheory.

Require Import Tactics.

Module SIT_Properties (Import sit : ShallowIntersectionTheory).
  Definition full : perm -> Prop :=
    fun a => forall a', compl a a' -> empty a'.
  Hint Unfold full.

  Instance full_respectful : Proper (equiv ==> iff) full.
   repeat intro; unfold full; intuition; ssubst; auto.
  Qed.
  Hint Resolve ax_empty_unique.
  Hint Resolve ax_compl_symmetric.
  Hint Resolve ax_compl_empty_inter.

  Ltac use_uniqueness :=
    match goal with
    | H : empty ?a, H' : empty ?b |- _ => assert (a == b) by auto; clear H'; ssubst
    | H : compl ?a ?a', H' : compl ?a ?b' |- _ => assert (a' == b') by (eapply ax_compl_functional; eauto); clear H'; ssubst
    | H : compl ?a' ?a, H' : compl ?b' ?a |- _ => assert (a' == b') by (eapply ax_compl_functional; eauto); clear H'; ssubst
    | H : inter ?a ?b ?ab, H' : inter ?a ?b ?ab' |- _ => assert (ab == ab) by (eapply ax_inter_functional; eauto); clear H'; ssubst
    end.

  Ltac complements := repeat
    match goal with
    | a : perm |- _ => lazymatch goal with
      | H : compl a ?a' |- _ => fail
      | H : compl ?a' a |- _ => fail
      | _ => let a' := fresh a "'" in destruct (ax_compl_total a) as [a'] end
    end.

  Lemma full_unique : forall a, full a -> forall b, full b -> a == b.
   unfold full; intros; complements; use_foralls; intuition.
   repeat use_uniqueness; reflexivity.
  Qed.

  Lemma full_inter : forall a b, full a -> inter a b b.
   intros.
   complements.
   intuition eauto.
  Qed.

  Hint Resolve ax_compl_irreflexive.

  Lemma full_not_empty : forall a, full a -> ~ empty a.
   cbv.
   intros; complements; use_foralls; intuition.
   repeat use_uniqueness.
   eapply ax_compl_irreflexive; eauto.
  Qed.

End SIT_Properties.


Require Import LList.
Require Import List.

Section InhabitationFunctionDefs.
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

Section DeepPermissions.

  Inductive dpf : nat -> Set :=
    | dpf_false : forall n, dpf n
    | dpf_and : forall n, dpf n -> dpf n -> dpf n
    | dpf_or : forall n, dpf n -> dpf n -> dpf n
    | dpf_not : forall n, dpf n -> dpf n
    | dpf_eq : forall n, forall n0, n > n0 -> forall n1, n > n1 -> dpf n
    | dpf_inter : forall n, forall n0, n > n0 -> forall n1, n > n1 -> forall n2, n > n2 -> dpf n
    | dpf_empty : forall n, forall n0, n > n0 -> dpf n
    | dpf_compl : forall n, forall n0, n > n0 -> forall n1, n > n1 -> dpf n
    | dpf_all : forall n, dpf (S n) -> dpf n
    | dpf_ex : forall n, dpf (S n) -> dpf n.

End DeepPermissions.


(* *)


  Program Fixpoint select_in n (l : llist bool n) i (H : n > i) t : Prop :=
    match l as m with
    | nil => False
    | cons b bs => match i with
      | O => b = t
      | S i' => @select_in (match n with O => _ | S n' => n' end) bs i' _ t
      end
    end.
  Next Obligation.
   destruct l.
   simpl in *.
   destruct x;
   inversion Heq_m; subst.
   reflexivity.
  Qed.
  Next Obligation.
   destruct l; destruct x; inversion Heq_m.
   subst.
   simpl in *.
   apply Gt.gt_S_n; trivial.
  Qed.

  (* a and b are equal iff
    a /\ b' = 0 and a' /\ b = 0 *)
  Definition equal_in_inhf n (ps : inhf n) v0 (H0 : n > v0) v1 (H1 : n > v1) : Prop :=
   (forall l, select_in l H0 true -> select_in l H1 false -> ps l = false) /\
   (forall l, select_in l H0 false -> select_in l H1 true -> ps l = false).

  (* a /\ b = c iff
        a /\ b /\ c' = 0    -- c includes all of a /\ b
    and a' /\ c = 0         -- all of c is in a
    and b' /\ c = 0         -- all of c is in b
  *)
  Definition inter_in_inhf n (ps : inhf n) v0 (H0 : n > v0) v1 (H1 : n > v1)
                   v2 (H2 : n > v2) : Prop :=
   (forall l, select_in l H0 true -> select_in l H1 true ->
               select_in l H1 false -> ps l = false) /\
   (forall l, select_in l H0 false -> select_in l H2 true -> ps l = false) /\
   (forall l, select_in l H1 false -> select_in l H2 true -> ps l = false).

  (* a and b are complements iff
    a /\ b = 0 and a' /\ b' = 0 *)
  Definition compl_in_inhf n (ps : inhf n) v0 (H0 : n > v0) v1 (H1 : n > v1) : Prop :=
    (forall l, select_in l H0 true -> select_in l H1 true -> ps l = false) /\
    (forall l, select_in l H0 false -> select_in l H1 false -> ps l = false).

  Definition empty_in_inhf n (ps : inhf n) v0 (H0 : n > v0) : Prop :=
    (forall l, select_in l H0 true -> ps l = false).
               
  Fixpoint dpf_true n (f : dpf n) : inhf n -> Prop :=
    match f with
    | dpf_false _ => fun _ => False
    | dpf_and _ l r => fun ps => dpf_true l ps /\ dpf_true r ps
    | dpf_or _ l r => fun ps => dpf_true l ps \/ dpf_true r ps
    | dpf_not _ f' => fun ps => ~ dpf_true f' ps
    | dpf_eq m n0 H0 n1 H1 => fun ps => equal_in_inhf ps H0 H1
    | dpf_inter m n0 H0 n1 H1 n2 H2 => fun ps => inter_in_inhf ps H0 H1 H2
    | dpf_compl m n0 H0 n1 H1 => fun ps => compl_in_inhf ps H0 H1
    | dpf_empty m n0 H0 => fun ps => empty_in_inhf ps H0
    | dpf_all m f' => fun ps => forall ps', is_extension_of ps' ps -> dpf_true f' ps'
    | dpf_ex m f' => fun ps => exists ps', is_extension_of ps' ps -> dpf_true f' ps'
    end.

Module DeepPermissionEmbedding (Import sit : ShallowIntersectionTheory).

  Fixpoint dpf_emb n (f : dpf n) : (llist perm n) -> Prop :=
    match f with
    | dpf_false _ => fun _ => False
    | dpf_and _ l r => fun ps => dpf_emb l ps /\ dpf_emb r ps
    | dpf_or _ l r => fun ps => dpf_emb l ps \/ dpf_emb r ps
    | dpf_not _ f' => fun ps => ~ dpf_emb f' ps
    | dpf_eq n n0 H0 n1 H1 => fun ps => llget ps H0 == llget ps H1
    | dpf_inter n n0 H0 n1 H1 n2 H2 => fun ps => inter (llget ps H0) (llget ps H1) (llget ps H2)
    | dpf_empty n n0 H0 => fun ps => empty (llget ps H0)
    | dpf_compl n n0 H0 n1 H1 => fun ps => compl (llget ps H0) (llget ps H1) 
    | dpf_all m f' => fun ps => forall p, dpf_emb f' (llcons p ps)
    | dpf_ex m f' => fun ps => exists p, dpf_emb f' (llcons p ps)
    end.

(*
  Program Definition tf1 : dpf 0 :=
    dpf_all (dpf_ex (dpf_eq (n0:=0) _ (n1:=1) _)).

  Lemma tf1_holds : (dpf_emb tf1 (llnil _)).
   cbv -[equiv].
   intro p.
   exists p; reflexivity.
  Qed.
*)
(*
  Inductive perm_term :=
   | pt_full : perm_term
   | pt_empty : perm_term
   | pt_literal : perm -> perm_term
   | pt_compl : perm_term -> perm_term
   | pt_inter : perm_term -> perm_term -> perm_term.

  Fixpoint is_empty_term (p : perm) (pt : perm_term) : Prop :=
    match pt with
    | pt_full => empty p
    | pt_empty => True
    | pt_literal l => forall x, inter p l x -> empty x
    | pt_compl t => is_nonempty_term 
*)

  Program Fixpoint intersections_empty p n (l : llist bool n) : (llist perm n) -> Prop :=
   match n with
   | O => fun _ => empty p
   | S n' => fun ps => match @llhead _ (n') l with
         | false => forall pq, inter p (llhead ps) pq -> @intersections_empty pq n' (lltail l) (lltail ps)
         | true => forall q', compl (llhead ps) q' -> forall pq', inter p q' pq' ->
                     @intersections_empty pq' n' (lltail l) (lltail ps)
         end
   end.
  Next Obligation.
   destruct l; intuition.
  Qed.
  Next Obligation.
   destruct l; firstorder.
  Qed.
  Next Obligation.
   destruct l; firstorder.
  Qed.

  Program Fixpoint intersections_nonempty p n (l : llist bool n) : (llist perm n) -> Prop :=
   match n with
   | O => fun _ => ~empty p
   | S n' => fun ps => match @llhead _ (n') l with
         | false => forall pq, inter p (llhead ps) pq -> intersections_nonempty pq (lltail l) (lltail ps)
         | true => forall q', compl (llhead ps) q' -> forall pq', inter p q' pq' ->
                     intersections_nonempty pq' (lltail l) (lltail ps)
         end
   end.
  Next Obligation.
   destruct l; intuition.
  Qed.
  Next Obligation.
   destruct l; firstorder.
  Qed.
  Next Obligation.
   destruct l; firstorder.
  Qed.

  Module Import sp := (SIT_Properties sit).

  Definition inter_empty n l ps := forall F, full F -> @intersections_empty F n l ps.
  Definition inter_nonempty n l ps := forall F, full F -> @intersections_nonempty F n l ps.

  Definition inhf_props n (I : inhf n) (ps : llist perm n) : Prop :=
   forall l, if I l then inter_nonempty l ps else inter_empty l ps.

  Theorem dpf_true_emb n : forall (f : dpf n) (I : inhf n) (ps : llist perm n),
        inhf_props I ps -> (dpf_true f I <-> dpf_emb f ps).
   induction f; intuition.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.
    firstorder.

    (* eq -> *)
    simpl in *.
    set (llget ps g); set (llget ps g0);
    complements.
    eapply ax_inter_equiv; eauto.
    firstorder.
    unfold equal_in_inhf in H0.
    unfold inhf_props in H.
    

    firstorder.

    simpl in *.
    contradict H.
    firstorder.
    intro; contradict H.
    firstorder.
    simpl in *.
    firstorder.
End DeepPermissionEmbedding. 
