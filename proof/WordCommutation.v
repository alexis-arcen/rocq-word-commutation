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

Fixpoint prefixe (k : nat) (u : word) : word :=
  match k, u with
  | 0, _ => epsilon
  | S k', epsilon => epsilon
  | S k', cons x u' => cons x (prefixe k' u')
  end.

Declare Scope word_scope.
Bind Scope word_scope with word.
Open Scope word_scope.

Notation "x :: u" := (cons x u) : word_scope.
Notation "| u |" := (len u) (at level 10) : word_scope.
Notation "u ++ v" := (conc u v) : word_scope.
Notation "u ^ n" := (pow n u) : word_scope.

Section Combinatorics.

Lemma conc_nil_l : forall (u : word), u = u ++ epsilon.
Proof.
  intro u. induction u as [| x u' IHu'].
  - reflexivity.
  - simpl. rewrite <- IHu'. reflexivity.
Qed.

Lemma conc_assoc : forall (u v w : word),
  u ++ (v ++ w) = (u ++ v) ++ w.
Proof.
  intros u v w. induction u as [| x u' IHu'].
  - reflexivity.
  - simpl. rewrite -> IHu'. reflexivity.
Qed.

Lemma len_0 : forall (u : word), |u| = 0 -> u = epsilon.
Proof.
  intro u. destruct u as [| x u'] eqn:E.
  - intro H. reflexivity.
  - intro H. simpl in H. discriminate.
Qed.

Lemma pref_first_word : forall (u v : word),
  prefixe (|u|) (u ++ v) = u.
Proof.
  intros u v. induction u as [| x u' IHu'].
  - reflexivity.
  - simpl. rewrite -> IHu'. reflexivity.
Qed.

End Combinatorics.

Section Arithmetics.

Lemma add_0_r  : forall (n : nat), n + 0 = n.
Proof.
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - apply eq_S in IHn'. rewrite -> plus_Sn_m. exact IHn'.
Qed.

Lemma plus_comm : forall (m n : nat), m + n = n + m.
Proof. 
  intros m n. induction m as [| m' IHm'].
  - simpl. apply plus_n_O. 
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHm'. reflexivity.
Qed.

Lemma zero_split : forall (m n : nat), m + n = 0 -> m = 0 /\ n = 0.
Proof. 
  intros m n. destruct m as [| m'].
  - intro H. split. reflexivity. exact H.
  - intro H. simpl in H. inversion H.
Qed.

Lemma gt_to_le : forall (m n : nat), n > m -> m <= n.
Proof. 
  intros m n H. unfold gt in H. unfold lt in H. apply le_S_n.
  apply le_S. exact H.
Qed.

Lemma int_strict_positive : forall (n : nat), S n > 0.
Proof.
  intro n. unfold gt. unfold lt. induction n as [| n'].
  - apply le_n.
  - apply le_S in IHn'. exact IHn'.
Qed.

Lemma succ_pos_strict : forall (n : nat), n < S n.
Proof. intro n. unfold lt. apply le_n. Qed.

Lemma sup_succ_strict : forall (m n : nat), S m > S n -> m > n.
Proof.
  intros m n H. unfold gt. unfold lt. unfold gt in H. unfold lt in H.
  apply le_S_n in H. exact H.
Qed.

Lemma lt_S : forall (m n : nat), n < m -> n < S m.
Proof. 
  intros m n H. unfold lt in H. unfold lt. apply le_S in H.
  exact H.
Qed.

Lemma lt_add_S_l_r : forall (m n : nat), m < n -> S m < S n.
Proof.
  intros m n H. unfold lt in H. unfold lt. apply le_n_S. exact H.
Qed.

Lemma lt_add_n_l_r : forall (m n o : nat), o < m -> o+n < m+n.
Proof.
  intros m n o. induction n as [| n' IHn'].
  - intro H. do 2 rewrite -> add_0_r. exact H.
  - intro H. do 2 rewrite <- plus_n_Sm. apply lt_add_S_l_r.
    apply IHn'. exact H.
Qed.

Lemma lt_le_trans : forall (m n o : nat), m < n /\ n <= o -> m < o.
Proof.
  unfold lt. intros m n o H. destruct H as [H1 H2]. 
  induction H2 as [| o' IHo'1 IHo'2].
  - exact H1.
  - apply le_S. exact IHo'2.
Qed.

Lemma remove_S_keep_o_n : forall (m n o k : nat),
  m + n <= S k /\ o < m -> o + n <= k.
Proof. 
  intros m n o k H. destruct H as [H1 H2].
  apply lt_add_n_l_r with (o := o) (m := m) (n := n) in H2.
  assert (o + n < m + n /\ m + n <= S k) as H3. split; assumption.
  apply lt_le_trans  in H3. unfold lt in H3.
  apply le_S_n in H3. exact H3.
Qed.

Lemma remove_S_keep_m_o : forall (m n o k : nat),
  m + n <= S k /\ o < n -> m + o <= k.
Proof. 
  intros m n o k H. destruct H as [H1 H2].
  assert (o + m < n + m) as H3. apply lt_add_n_l_r. exact H2.
  replace (m+n) with (n+m) in H1.
  assert (o + m < n + m /\ n + m <= S k) as H4. split; assumption.
  apply lt_le_trans  in H4. apply le_S_n in H4.
  replace (m+o) with (o+m). exact H4. all: apply plus_comm.
Qed.

Lemma le_disjunction : forall (m n : nat), m <= n -> m = n \/ m < n.
Proof.
  intro m. induction m as [| m' IHm'].
  - intro n. destruct n as [| n'].
    + intro H. left. reflexivity.
    + intro H. right. pose proof (int_strict_positive n') as H1.
    unfold gt in H1. exact H1.
  - intro n. destruct n as [| n'].
    + intro H. inversion H.
    + intro H. specialize (IHm' n'). apply le_S_n in H.
      apply IHm' in H. case H as [H1 | H2].
      * left. apply eq_S. exact H1.
      * right. unfold lt. unfold lt in H2. apply le_n_S in H2.
        exact H2.
Qed.

Lemma cases_int : forall (m n : nat), m = n \/ m > n \/ m < n.
Proof.
  intros m n. induction m as [| m' IHm'].
  - destruct n as [| n'] eqn:E.
    + left. reflexivity.
    + right. right. pose proof (int_strict_positive n') as H.
      unfold gt in H. exact H.
  - destruct IHm' as [H1 | [H2 | H3]].
    + right. left. rewrite -> H1. unfold gt. apply succ_pos_strict.
    + right. left. unfold gt. unfold lt. unfold gt in H2.
      unfold lt in H2. apply le_S in H2. exact H2.
    + unfold lt in H3. assert (S m' <= n -> S m' = n \/ S m' < n) as H.
      apply le_disjunction with (m := S m') (n := n).
      apply H in H3. case H3.
      * intro H1. left. exact H1.
      * intro H1. right. right. exact H1.
Qed.

End Arithmetics.

Section Fine_Wilf.

Lemma pref_inside_first : forall (k : nat) (u v : word),
  k <= |u| -> prefixe k (u ++ v) = prefixe k u.
Proof.
  intro k. induction k as [| k' IHk'].
  - intros u v H. reflexivity.
  - intros u v. induction u as [| x u' IHu'].
    + intro H. simpl in H. inversion H.
    + intro H. simpl in H. apply le_S_n in H.
      specialize (IHk' u' v H). simpl. rewrite IHk'. reflexivity.
Qed.

Lemma case_egal1_generalized : forall (u v w1 w2 : word),
  |u| = |v| -> u ++ w1 = v ++ w2 -> u = v.
Proof.
  intro u. induction u as [| x1 u' IHu'].
  - intros v w1 w2 H1 H2. simpl in H1. symmetry in H1.
    apply len_0 in H1. symmetry. exact H1.
  - intro v. destruct v as [| x2 v'] eqn:E.
    + intros w1 w2 H1 H2. simpl in H1. inversion H1.
    + intros w1 w2 H1 H2. simpl in H1. injection H2. intro H3.
      simpl in H1. injection H1. intros H4 H5.
      subst x2. f_equal. apply IHu' with (w1 := w1) (w2 := w2).
      exact H4. exact H3.
Qed.

Lemma case_egal1 : forall (u v : word) (x : letter),
  |u| = |v| -> u ++ (x :: v) = v ++ (x :: u) -> u ++ v = v ++ u.
Proof.
  intros u v x H1 H2.
  pose proof (case_egal1_generalized u v (x :: v) ( x :: u)) as H3.
  apply H3 in H1. subst v. reflexivity. exact H2.
Qed.

Lemma case_egal : forall (u v : word),
  (|u| = |v| /\ u ++ v = v ++ u) -> u = v.
Proof.
  intro u. induction u as [| x1 u' IHu'].
  - intros v H. destruct H as [H1 H2]. simpl in H2. simpl in H1. 
    symmetry in H1. apply len_0 in H1. symmetry. exact H1.
  - intros v H. destruct H as [H1 H2]. induction v as [| x2 v' IHv'].
    + simpl in H1. inversion H1.
    + simpl in H1. apply eq_add_S in H1. simpl in H2. injection H2.
      intros H3 H4. symmetry in H2. subst x2.
      assert (|u'| = |v'| -> u' ++ (x1 :: v') = v' ++ (x1 :: u')) as H4. 
      * intro H4. exact H3.
      * apply case_egal1 in H4. f_equal.
        assert (|u'| = |v'| /\ u' ++ v' = v' ++ u') as H5.
        split; assumption. specialize (IHu' v'). apply IHu' in H5.
        exact H5. all: exact H1.
Qed.

Lemma three_cases : forall (u v : word),
  |u| = |v| \/ |u| > |v| \/ |u| < |v|.
Proof. intros u v. apply cases_int. Qed.

Lemma conc_egal_2 : forall (u v1 v2 : word),
  u ++ v1 = u ++ v2 -> v1 = v2.
Proof.
  intros u v1 v2. induction u as [| x u' IHu'].
  - intro H. simpl in H. exact H.
  - intros H1. simpl in H1. injection H1. intro H2.
    apply IHu'. exact H2.
Qed.

Lemma conc_pow : forall (m n : nat) (u : word),
  u^m ++ u^n = u^(m + n).
Proof.
  intros m n u. induction m as [| m' IHm'].
  - reflexivity.
  - simpl. rewrite <- conc_assoc. rewrite IHm'. reflexivity.
Qed.

Lemma empty_or_larger : forall (v : word), v = epsilon \/ |v| > 0.
Proof.
  intro v. destruct v as [|x v'] eqn:E.
  - left. reflexivity.
  - right. simpl. apply int_strict_positive.
Qed.

Lemma pref_cut : forall (u v : word),
  |u| > |v| /\ |v| > 0 /\ prefixe (|v|) u = v -> 
  exists (w : word), |w| < |u| /\ u = v ++ w.
Proof.
  intros u v. revert u. induction v as [| x2 v' IHv'].
  - intros u H. destruct H as [H1 H2]. destruct H2 as [H2 H3].
    inversion H2.
  - intro u. destruct u as [| x1 u'] eqn:E.
    + intro H. destruct H as [H1 H2]. inversion H1.
    + intro H. destruct H as [H1 [H2 H3]]. injection H3. intros H4 H5.
      subst x2. pose proof (empty_or_larger v') as H5. simpl. case H5.
      clear H2 H3 H5.
      * intro H6. rewrite H6. exists u'. split. apply succ_pos_strict.
        reflexivity.
      * intro H6.
        assert (|u'| > |v'| /\ |v'| > 0 /\ prefixe (|v'|) u' = v') as H7.
        repeat split. simpl in H1. apply sup_succ_strict in H1. exact H1.
        exact H6. exact H4. clear H1 H6 H4. 
        specialize (IHv' u' H7). destruct IHv' as [w H8]. exists w.
        destruct H8 as [H8 H9]. apply lt_S in H8. split. exact H8.
        f_equal. exact H9.
Qed.

Lemma fine_wilf_aux : forall (k : nat) (u v : word),
  ((|u| + |v| <= k) /\ u ++ v = v ++ u) -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  intro k. induction k as [| k' IHk'].
  - intros u v H. destruct H as [H1 H2]. inversion H1. exists v , 0, 0.
    simpl. apply zero_split in H0. destruct H0 as [H3 H4].
    apply len_0 in H3, H4. split. exact H3. exact H4.
  - intros u v. pose proof (three_cases u v) as H.
    destruct H as [HCASE_1 | [HCASE_2 | HCASE_3]].
    + intro H. destruct H as [H1 H2].
      assert (|u| = |v| /\ u ++ v = v ++ u) as H3. split; assumption.
      apply case_egal in H3. exists u, 1, 1.
      split; simpl; rewrite <- conc_nil_l. reflexivity. symmetry.
      exact H3.
    + intro H1. pose proof (empty_or_larger v) as H2. case H2.
      * intro H3. exists u, 0, 1. simpl. split. rewrite <- conc_nil_l.
        reflexivity. exact H3.
      * intro H3. destruct H1 as [H1 H4].
        apply gt_to_le in HCASE_2 as H5.
        specialize (pref_inside_first (|v|) u v H5). intro H6.
        rewrite H4 in H6. rewrite -> pref_first_word in H6. symmetry in H6.
        assert (|u| > |v| /\ |v| > 0 /\ prefixe (|v|) u = v) as H7.
        repeat split; assumption. apply pref_cut in H7.
        destruct H7 as [u' H7]. destruct H7 as [H7 H8]. rewrite H8 in H4.
        rewrite <- conc_assoc in H4. apply conc_egal_2 in H4.
        assert (|u| + |v| <= S k' /\ |u'| < |u|) as H9. split; assumption.
        specialize (remove_S_keep_o_n (|u|) (|v|) (|u'|) k' H9). intro H10.
        assert (|u'| + |v| <= k' /\ u' ++ v = v ++ u') as H11.
        split; assumption. apply IHk' in H11.
        destruct H11 as [w [n [m H11]]]. destruct H11 as [H11 H12].
        rewrite H11, H12 in H8. rewrite conc_pow in H8.
        exists w, n, (n + m). split. exact H8. exact H12.
    + intro H1. pose proof (empty_or_larger u) as H2. case H2.
      * intro H3. exists v, 1, 0. simpl. split. exact H3.
        rewrite <- conc_nil_l. reflexivity.
      * intro H3. destruct H1 as [H1 H4].
        apply gt_to_le in HCASE_3 as H5.
        specialize (pref_inside_first (|u|) v u H5). intro H6.
        rewrite <- H4 in H6. rewrite pref_first_word in H6. symmetry in H6.
        assert (|v| > |u| /\ |u| > 0 /\ prefixe (|u|) v = u) as H7.
        repeat split; assumption. apply pref_cut in H7.
        destruct H7 as [v' H7]. destruct H7 as [H7 H8]. rewrite H8 in H4.
        rewrite <- conc_assoc in H4. apply conc_egal_2 in H4.
        assert (|u| + |v| <= S k' /\ |v'| < |v|) as H9. split; assumption.
        specialize (remove_S_keep_m_o (|u|) (|v|) (|v'|) k' H9). intro H10.
        assert (|u| + |v'| <= k' /\ u ++ v' = v' ++ u) as H11.
        split; assumption. apply IHk' in H11.
        destruct H11 as [w [n [m H11]]]. destruct H11 as [H11 H12].
        rewrite H11, H12 in H8. rewrite conc_pow in H8.
        exists w, (m + n), m. split; assumption.
Qed.

Theorem fine_wilf : forall (u v : word),
  u ++ v = v ++ u -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  intros u v H1. pose proof (fine_wilf_aux (|u| + |v|) u v) as H2.
  assert (|u| + |v| <= |u| + |v| /\ u ++ v = v ++ u) as H4. split.
  apply le_n. exact H1. apply H2 in H4. destruct H4 as [w [n [m H4]]].
  exists w, n, m. exact H4.
Qed.

End Fine_Wilf.