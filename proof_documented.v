(* This one file contains the whole documented proof. It is divided
into four different sections, each with their name and description. 

You do not need to install any external Rocq libraries.

Furthermore we shall assume the lemmas below, provided by Rocq,
are already proven:
- eq_S
- plus_Sn_m
- plus_n_Sm 
- le_S_n
- le_n_S 

And before reading the proofs documentation, it is highly recommended to
fully understand Rocq's definition of <, >, <= and >=. 
*)

Print le. Print lt. Print ge. Print gt.

(* Here are the different definitions used in this proof.*)
Inductive letter : Type :=
  | a : letter
  | b : letter
  | c : letter.

Inductive word : Type :=
  | epsilon : word
  | cons : letter -> word -> word.

Fixpoint conc (u v : word) : word :=
  match u with
  | epsilon => v
  | cons x u => cons x (conc u v)
  end.

Fixpoint len (u : word) : nat :=
  match u with
  | epsilon => 0
  | cons x u' => 1 + (len u')
  end.

Fixpoint pow (n : nat) (u : word) : word :=
  match n with
  | 0 => epsilon
  | S n' => conc u (pow n' u)
  end.

Fixpoint prefix (k : nat) (u : word) : word :=
  match k, u with
  | 0, _ => epsilon
  | S k', epsilon => epsilon
  | S k', cons x u' => cons x (prefix k' u')
  end.

Declare Scope word_scope.
Bind Scope word_scope with word.
Open Scope word_scope.

Notation "x :: u" := (cons x u) : word_scope.
Notation "| u |" := (len u) (at level 10) : word_scope.
Notation "u ++ v" := (conc u v) : word_scope.
Notation "u ^ n" := (pow n u) : word_scope.

(* This section contains basic lemmas used in Arithmetics. *)
Section Arithmetics.

Lemma add_0_r : forall (n : nat), n + 0 = n.
Proof. induction n; [reflexivity | rewrite plus_Sn_m; f_equal; assumption]. Qed.

Lemma plus_comm : forall (m n : nat), m + n = n + m.
Proof. induction m as [| m' IHm']; intro n; [rewrite add_0_r | rewrite plus_Sn_m, <- plus_n_Sm, IHm']; reflexivity. Qed.

Lemma zero_split : forall (m n : nat), m + n = 0 -> m = 0 /\ n = 0.
Proof. 
  intros [| m'] n H.
  - split; [reflexivity | exact H].
  - inversion H. 
(* [inversion H] : Rocq evaluates S m' + n to S (m' + n) thanks to [+]
definition. It then sees that each side of the equality was made with a
different nat constructor. Since constructors are by definition mutually
disjoint, these two elements cannot be equal. The hypothesis H is therefore
equivalent to False. [inversion H] detects this contradiction and automatically
concludes the proof. *)
Qed.

Lemma gt_to_le : forall (m n : nat), n > m -> m <= n.
Proof. intros m n H. apply le_S_n, le_S; assumption. Qed.

Lemma int_strict_positive : forall (n : nat), S n > 0.
Proof. induction n; [ apply le_n | apply le_S; assumption]. Qed.

Lemma succ_pos_strict : forall (n : nat), n < S n.
Proof. intro n. apply le_n. Qed.

Lemma sup_succ_strict : forall (m n : nat), S m > S n -> m > n.
Proof. intros m n H. exact (le_S_n _ _ H). Qed.

Lemma lt_S : forall (m n : nat), n < m -> n < S m.
Proof. intros m n H. exact (le_S _ _ H). Qed.

Lemma lt_add_S_l_r : forall (m n : nat), m < n -> S m < S n.
Proof. intros m n H. apply le_n_S. assumption. Qed.

Lemma lt_add_n_l_r : forall (m n o : nat), o < m -> o+n < m+n.
Proof. intros m n o H. induction n; [rewrite !add_0_r | rewrite <- !plus_n_Sm; apply lt_add_S_l_r]; assumption. Qed.

Lemma lt_le_trans : forall (m n o : nat), m < n /\ n <= o -> m < o.
Proof. intros m n o [H1 H2]. induction H2; [| apply le_S]; assumption. Qed.

Lemma remove_S_keep_o_n : forall (m n o k : nat),
  m + n <= S k /\ o < m -> o + n <= k.
Proof. 
  intros m n o k [H1 H2].
  apply le_S_n, (lt_le_trans _ (n + m) _).
  rewrite (plus_comm n m).
  split; [apply lt_add_n_l_r |]; assumption.
Qed.

Lemma remove_S_keep_m_o : forall (m n o k : nat),
  m + n <= S k /\ o < n -> m + o <= k.
Proof. 
  intros m n o k [H1 H2].
  rewrite plus_comm.
  apply le_S_n, (lt_le_trans _ (n + m) _).
  split; [apply lt_add_n_l_r | rewrite plus_comm ]; assumption.
Qed.

Lemma le_disjunction : forall (m n : nat), m <= n -> m = n \/ m < n.
Proof. intros m n H. destruct H; [left; reflexivity | right; apply le_n_S; assumption]. Qed. 
  
Lemma cases_int : forall (m n : nat), m = n \/ m > n \/ m < n.
Proof.
  intros m n. induction m as [| m' IHm'].
  - destruct n; [left; reflexivity | do 2 right; exact (int_strict_positive n)].
  - destruct IHm' as [H1 | [H2 | H3]].
    + right; left; rewrite H1; apply succ_pos_strict.
    + right; left; apply le_S in H2; exact H2.
    + destruct (le_disjunction _ _ H3); [left | do 2 right]; assumption.
Qed.

End Arithmetics.

(* This section contains basic lemmas used in Combinatorics of 
Words *)
Section Combinatorics.

Lemma conc_nil_r : forall (u : word), u = u ++ epsilon.
Proof. induction u as [| x u' IHu']; [| simpl; rewrite <- IHu']; reflexivity. Qed.

Lemma conc_assoc : forall (u v w : word), u ++ (v ++ w) = (u ++ v) ++ w.
Proof. intros u v w; induction u as [| x u' IHu']; [| simpl; rewrite IHu']; reflexivity. Qed.

Lemma len_0 : forall (u : word), |u| = 0 -> u = epsilon.
Proof. destruct u; intro H; [reflexivity | discriminate]. Qed.

Lemma empty_or_larger : forall (v : word), v = epsilon \/ |v| > 0.
Proof. intro v. destruct v; [left; reflexivity | right; apply int_strict_positive]. Qed.

Lemma pref_first_word : forall (u v : word),
  prefix (|u|) (u ++ v) = u.
Proof. intros u v; induction u as [| x u' IHu']; [| simpl; rewrite IHu']; reflexivity. Qed.

Lemma pref_inside_first : forall (k : nat) (u v : word),
  k <= |u| -> prefix k (u ++ v) = prefix k u.
Proof.
  induction k as [| k' IHk'].
  - reflexivity.
  - intros [| x u'] v H; [inversion H | apply le_S_n in H; simpl; f_equal; apply IHk'; assumption].
    (* [inversion H] : Rocq evaluates |epsilon| to 0 by the definition of [len].
    0 cannot be the successor of a nat. Therefore H <-> False. The proof
    is concluded. *)
Qed.

Lemma pref_cut : forall (u v : word),
  |u| > |v| /\ |v| > 0 /\ prefix (|v|) u = v -> 
  exists (w : word), |w| < |u| /\ u = v ++ w.
Proof.
  intros u v; revert u; induction v as [| x2 v' IHv'].
  - intros u [_ [H _]]; inversion H.
    (* [inversion H] : Rocq evaluates |epsilon| to 0 and because 0 > 0
    is an empty type according to [lt] definiton, H <-> False. The proof
    is concluded. *)

  - destruct u as [| x1 u'].
    + intros [H _]. inversion H.
    (* [inversion H] : Same as above but this time Rocq evaluates
    | x2 :: v' | to S (| v' |). *)

    + intros [H1 [H2 H3]]. injection H3; intros H4 H5.
      (* [injection H3] : Since the constructor [cons] is by definition
      injective, Rocq splits the equation into two new equalities : one for
      the letters and one for the rest. *)

      subst x2; simpl; destruct (empty_or_larger v').
      * rewrite H; exists u'; split; [apply succ_pos_strict | reflexivity].
      * assert (H7 : |u'| > |v'| /\ |v'| > 0 /\ prefix (|v'|) u' = v') by (repeat split; [simpl in H1; apply sup_succ_strict in H1 | | ]; assumption).
        destruct (IHv' u' H7) as [w [H8 H9]]; apply lt_S in H8. 
        exists w; split; [| f_equal]; assumption.
Qed.

Lemma three_cases : forall (u v : word),
  |u| = |v| \/ |u| > |v| \/ |u| < |v|.
Proof. intros u v. apply cases_int. Qed.

Lemma conc_egal_2 : forall (u v1 v2 : word),
  u ++ v1 = u ++ v2 -> v1 = v2.
Proof. intros u v1 v2. induction u as [| x u' IHu']; intro H; [| injection H; intro; apply IHu']; assumption. Qed.
(* [injection H] : Same as [pref_cut]'s injection, but this time both x's are the same
so Rocq only needs to keep the second equality. *)

Lemma conc_pow : forall (m n : nat) (u : word),
  u^m ++ u^n = u^(m + n).
Proof. intros m n u. induction m as [| m' IHm']; [| simpl; rewrite <- conc_assoc, IHm']; reflexivity. Qed.

End Combinatorics.

(* Finally, this section contains the main proof. *)
Section Fine_Wilf.

Lemma case_egal1_generalized : forall (u v w1 w2 : word),
  |u| = |v| ->
  u ++ w1 = v ++ w2 ->
  u = v.
Proof.
  induction u as [| x1 u' IHu'].
  - intros v w1 w2 H1 H2; symmetry in H1 |- *; exact (len_0 _ H1).
  - intros [| x2 v'] w1 w2 H1 H2.
    + inversion H1.
      (* [inversion H1] Rocq evaluates |x1 :: u'| to S |u'| then |epsilon| to 0. 
      Since zero cannot be the successor of a nat, the proof is concluded.  *)

    + injection H1 as H3; injection H2 as H4 H5; subst x2; f_equal; exact (IHu' _ _ _ H3 H5). 
Qed.

Lemma case_egal1 : forall (u v : word) (x : letter),
  |u| = |v| ->
  u ++ (x :: v) = v ++ (x :: u) ->
  u ++ v = v ++ u.
Proof. intros u v x H1 H2; pose proof (case_egal1_generalized _ _ _ _ H1 H2); subst; reflexivity. Qed.
 
Lemma case_egal : forall (u v : word),
  (|u| = |v| /\ u ++ v = v ++ u) -> u = v.
Proof.
  induction u as [| x1 u' IHu'].
  - intros v [H1 H2]; symmetry in H1 |- *; exact (len_0 _ H1).
  - intros [| x2 v'] [H1 H2].
    + inversion H1.
    + injection H1 as H1; injection H2 as H2 H3; subst x2.
      f_equal; exact (IHu' v' (conj H1 (case_egal1 _ _ _ H1 H3))).
Qed.  

(* In order to prove the Commutation Lemma in its original form,
we first need to prove an auxiliary version of it, using a given natural
number k as the maximum sum of lengths of the words. We will then proceed
to do an induction on this number k. *)
Lemma fine_wilf_aux : forall (k : nat) (u v : word),
  (|u| + |v| <= k) /\ u ++ v = v ++ u -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  induction k as [| k' IHk'].
  - intros u v [H1 H2]. 
    inversion H1. exists v , 0, 0. unfold pow. 
    apply zero_split in H0. destruct H0 as [H3 H4].
    apply len_0 in H3, H4. split. 
    exact H3. exact H4.
    (* note : [inversion H1] allows us to to show |u| + |v| = 0. In this 
    tactic, Rocq unfolds the definition of [le] and finds [le_n] is the 
    only constructor with which H1 could have been made. 
    Zero is indeed not the successor of any natural number. *)

  (* For the inductive case we need to proceed by cases on the parity of
  |u| - |v|, hence the use of [three_cases]. *)  
  - intros u v; destruct (three_cases u v) as [HCASE_1 | [HCASE_2 | HCASE_3]].

    (* For case |u| = |v|, we just use [case_egal]. *)
    + intro H. destruct H as [H1 H2].
      assert (|u| = |v| /\ u ++ v = v ++ u) as H3.
      split; assumption. apply case_egal in H3. 
      exists u, 1, 1.
      split; unfold pow; rewrite <- conc_nil_r. 
      reflexivity. symmetry. exact H3.

    (* For case |u| > |v|, we proceed by cases on |v| by using
    [empty_or_larger]. *)
    + intro H1. pose proof (empty_or_larger v) as H2.
      case H2.
      * intro H3. exists u, 0, 1. unfold pow. split.
        rewrite <- conc_nil_r. reflexivity. exact H3.
      * intro H3. destruct H1 as [H1 H4].

        (* Now supposing |v| > 0, we first show [u] can be decomposed into [v]
        and another word [u']. *)
        apply gt_to_le in HCASE_2 as H5.
        specialize (pref_inside_first (|v|) u v H5).
        intro H6. rewrite H4 in H6.
        rewrite pref_first_word in H6. symmetry in H6.
        assert (|u| > |v| /\ |v| > 0 /\ prefix (|v|) u = v) as H7.
        repeat split; assumption. apply pref_cut in H7.
        destruct H7 as [u' H7]. 
        
        (* Then we show [v] and [u'] do commute. *)
        destruct H7 as [H7 H8]. rewrite H8 in H4.
        rewrite <- conc_assoc in H4. apply conc_egal_2 in H4.

        (* Finally we show |u'| + |v| <= k', by using [remove_S_keep_o_n], which
        allows us to use the inductive hypothesis on [u'] and [v] and conclude
        the proof for this second case. *)
        assert (|u| + |v| <= S k' /\ |u'| < |u|) as H9. split; assumption.
        specialize (remove_S_keep_o_n (|u|) (|v|) (|u'|) k' H9). intro H10.
        assert (|u'| + |v| <= k' /\ u' ++ v = v ++ u') as H11.
        split; assumption. apply IHk' in H11.
        destruct H11 as [w [n [m H11]]]. destruct H11 as [H11 H12].
        rewrite H11, H12 in H8. rewrite conc_pow in H8.
        exists w, n, (n + m). split. exact H8. exact H12.

    (* For this third and last case |u| < |v|, the reasoning is pretty much the 
    same as the second case, except we have to be careful on how [v] is constructed
    with [u] and [v']. *)
    + intro H1. pose proof (empty_or_larger u) as H2. case H2.
      * intro H3. exists v, 1, 0. unfold pow. split. exact H3.
        rewrite <- conc_nil_r. reflexivity.
      * intro H3. destruct H1 as [H1 H4].
        apply gt_to_le in HCASE_3 as H5.
        specialize (pref_inside_first (|u|) v u H5). intro H6.
        rewrite <- H4 in H6. rewrite pref_first_word in H6. symmetry in H6.
        assert (|v| > |u| /\ |u| > 0 /\ prefix (|u|) v = u) as H7.
        repeat split; assumption. apply pref_cut in H7.
        destruct H7 as [v' H7]. 
        
        destruct H7 as [H7 H8]. rewrite H8 in H4.
        rewrite <- conc_assoc in H4. apply conc_egal_2 in H4.
        
        assert (|u| + |v| <= S k' /\ |v'| < |v|) as H9. split; assumption.
        specialize (remove_S_keep_m_o (|u|) (|v|) (|v'|) k' H9). intro H10.
        assert (|u| + |v'| <= k' /\ u ++ v' = v' ++ u) as H11.
        split; assumption. apply IHk' in H11.
        destruct H11 as [w [n [m H11]]]. destruct H11 as [H11 H12].
        rewrite H11, H12 in H8. rewrite conc_pow in H8.
        exists w, (m + n), m. split; assumption.
Qed.

(* Lastly, to prove the Commutation Lemma in its form as stated in the
READ.me file, we simply use [fine_wilf_aux], given k = |u| + |v|. 
And by using [le_n] we can prove the property |u| + |v| <= |u| + |v|
is always true before concluding. *)
Theorem fine_wilf : forall (u v : word),
  u ++ v = v ++ u -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof. intros u v H. exact (fine_wilf_aux (|u| + |v|) u v (conj (le_n (|u| + |v|)) H)). Qed.

End Fine_Wilf.