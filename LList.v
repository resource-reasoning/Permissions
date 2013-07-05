
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
 

  Lemma llist_tail_cons A n a (l : llist A n) : lltail (llcons a l) = l.
   auto.
  Qed.


Lemma ll_cons_rev_snoc : forall A n (l : llist A n) a, llrev (llcons a l) = llsnoc (llrev l) a.
 auto.
Qed.

Lemma llist_ind1 A : forall P : (llist A 1 -> Type),
    (forall a, P (llcons a (llnil A))) -> (forall l, P l).
 intros.
 rewrite <- (llist_head_tail).
 generalize (lltail l); intro;
  llniltac.
 auto.
Defined.
Lemma llist_head_cons A n a (l : llist A n) : llhead (llcons a l) = a.
reflexivity.
Qed.

Lemma llist_cohead_snoc A n a (l : llist A n) : llcohead (llsnoc l a) = a.
induction l using llist_ind.
auto.
rewrite llist_snoc_cons.
rewrite <- IHl at 2.
rewrite llist_cohead.
auto.
Qed.

Lemma llhead_cohead A n (l : llist A (S n)) : llhead (llrev l) = llcohead l.
  rewrite <- (llist_cohead_cotail l).
  rewrite <- ll_snoc_rev_cons.
  rewrite llist_head_cons.
  rewrite llist_cohead_snoc.
  auto.
Qed.

Lemma llist_tail_snoc A n a (l : llist A (S n)) : lltail (llsnoc l a) = llsnoc (lltail l) a.
  revert n l; apply llist_indS; intros;
  auto.
Qed.

Hint Resolve llist_cotail.
Lemma ll_tail_rev_cotail A n (l : llist A (S n)) : lltail (llrev l) = llrev (llcotail l).
  revert n l; apply llist_indS; intros.
  auto.
  rewrite ll_cons_rev_snoc.
  rewrite llist_tail_snoc.
  rewrite H.
  rewrite <- ll_cons_rev_snoc.
  f_equal; auto.
Qed.
Hint Resolve ll_tail_rev_cotail.


Program Fixpoint llget A n (l : llist A n) m (H : n > m) : A :=
  match l with
  | nil => _
  | cons x xs => match m with O => x | S m' => @llget A (match n with O => _ | S n' => n' end) xs m' _ end
  end.
Next Obligation.
 destruct n.
  contradict H; firstorder.
  destruct l; destruct x; subst.
   inversion e.
   inversion Heq_l.
Qed.
Next Obligation.
 destruct l.
 simpl in *.
 destruct x0; inversion Heq_l; subst.
 auto.
Qed.
Next Obligation.
 destruct l; destruct x0; inversion Heq_l; subst.
 firstorder.
Qed.

 (*
Lemma twogt1 : 2 > 1.
firstorder.
Qed.

Compute (llget (llcons 1 (llcons 2 (llnil _))) twogt1).
*)
