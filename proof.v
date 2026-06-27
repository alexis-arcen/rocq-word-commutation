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
Qed.

Lemma pref_cut : forall (u v : word),
  |u| > |v| /\ |v| > 0 /\ prefix (|v|) u = v ->
  exists (w : word), |w| < |u| /\ u = v ++ w.
Proof.
  intros u v; revert u; induction v as [| x2 v' IHv'].
  - intros u [_ [H _]]; inversion H.
  - destruct u as [| x1 u'].
    + intros [H _]. inversion H.
    + intros [H1 [H2 H3]]. injection H3; intros H4 H5.
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

Lemma conc_pow : forall (m n : nat) (u : word),
  u^m ++ u^n = u^(m + n).
Proof. intros m n u. induction m as [| m' IHm']; [| simpl; rewrite <- conc_assoc, IHm']; reflexivity. Qed.

End Combinatorics.

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
    + injection H1 as H3; injection H2 as H4 H5; subst x2; f_equal; exact (IHu' _ _ _ H3 H5). 
Qed.

Lemma case_egal1 : forall (u v : word) (x : letter),
  |u| = |v| ->
  u ++ (x :: v) = v ++ (x :: u) ->
  u ++ v = v ++ u.
Proof. intros u v x H1 H2; rewrite (case_egal1_generalized _ _ _ _ H1 H2); reflexivity. Qed.
 
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

Lemma fine_wilf_aux : forall (k : nat) (u v : word),
  (|u| + |v| <= k) /\ u ++ v = v ++ u ->
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  induction k as [| k' IHk'].
  - intros u v [H1 H2]; inversion H1 as [H3 |].
    destruct (zero_split _ _ H3) as [H4 H5].
    exists v , 0, 0; exact (conj (len_0 _ H4) (len_0 _ H5)).
  - intros u v.
    destruct (three_cases u v) as [HCASE_1 | [HCASE_2 | HCASE_3]]; intros [H1 H2].
    + exists u, 1, 1; split; simpl; rewrite <- conc_nil_r; [reflexivity | symmetry; exact (case_egal _ _ (conj HCASE_1 H2))].
    + destruct (empty_or_larger v) as [H3 | H3].
      * exists u, 0, 1; simpl; split; [rewrite <- conc_nil_r; reflexivity | exact H3].
      * pose proof (pref_inside_first (|v|) u v (gt_to_le _ _ HCASE_2)) as H4.
        rewrite H2, pref_first_word in H4; symmetry in H4.
        destruct (pref_cut _ _ (conj HCASE_2 (conj H3 H4))) as [u' [H5 H6]].
        clear HCASE_2 H3 H4.
        rewrite H6, <- conc_assoc in H2; apply conc_egal_2 in H2.
        pose proof (remove_S_keep_o_n (|u|) (|v|) (|u'|) k' (conj H1 H5)) as H7.
        destruct (IHk' _ _ (conj H7 H2)) as [w [n [m [H8 H9]]]].
        rewrite H8, H9, conc_pow in H6.
        exists w, n, (n + m); split; assumption.
    + destruct (empty_or_larger u) as [H3 | H3].
      * exists v, 1, 0; simpl; split; [assumption | rewrite <- conc_nil_r; reflexivity].
      * pose proof (pref_inside_first (|u|) v u (gt_to_le _ _ HCASE_3)) as H4.
        rewrite <- H2, pref_first_word in H4; symmetry in H4.
        destruct (pref_cut _ _ (conj HCASE_3 (conj H3 H4))) as [v' [H5 H6]].
        clear HCASE_3 H3 H4.
        rewrite H6, <- conc_assoc in H2; apply conc_egal_2 in H2.
        pose proof (remove_S_keep_m_o (|u|) (|v|) (|v'|) k' (conj H1 H5)) as H7.
        destruct (IHk' _ _ (conj H7 H2)) as [w [n [m [H8 H9]]]].
        rewrite H8, H9, conc_pow in H6.
        exists w, (m + n), m; split; assumption.
Qed.

Theorem fine_wilf : forall (u v : word),
  u ++ v = v ++ u ->
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof. intros u v H. exact (fine_wilf_aux (|u| + |v|) _ _ (conj (le_n (|u| + |v|)) H)). Qed.

End Fine_Wilf.