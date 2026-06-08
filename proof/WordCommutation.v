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
  match k with
  |0 => epsilon
  |S k' => match u with
           |epsilon => epsilon
           |cons x u' => cons x (prefixe k' u')
           end
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
  - intro. reflexivity.
  - intro. simpl in H. discriminate.
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
    + intro H. right. assert (S n' > 0) as H1.
      apply int_strict_positive. unfold gt in H1. exact H1.
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
    + right. right. assert (S n' > 0) as H. apply int_strict_positive.
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
  k<=|u| -> prefixe k (u ++ v) = prefixe k u.
Proof.
  intro k. induction k.
  - intros. simpl. reflexivity.
  - intro u. intro v. induction u.
    + intros. simpl in H. inversion H.
    + intros. simpl in H. apply le_S_n in H. specialize (IHk u v H). 
       simpl. rewrite IHk. reflexivity.
Qed.

Lemma case_egal11 : 
  forall (u v w1 w2 : word), |u| = |v| -> u ++ w1 = v ++ w2 -> u = v.
Proof.
  intro u. induction u.
  - intros. simpl in H. symmetry in H. apply len_0 in H. symmetry. assumption.
  - intro v. destruct v. 
    + intros. simpl in H. inversion H.
    + intros. simpl in H. injection H. intro. simpl in H0. injection H0. intros. symmetry in H3.
      subst. f_equal. apply IHu with (w1:=w1) (w2:=w2). assumption. assumption.
Qed.

Lemma case_egal1 :
forall (u v : word) (l : letter), |u| = |v| -> u ++ (cons l v) = v ++ (cons l u) -> u++v = v++u.
Proof.
  intros. assert (u = v).
  apply case_egal11 with (w1 := cons l v) (w2 := cons l u). assumption. assumption.
  rewrite H1. reflexivity.
Qed.

Lemma case_egal :
  forall (u v : word), (|u|=|v| /\ u++v = v++u) -> u=v.
Proof.
  intro u. induction u.
   - intros. destruct H. simpl in H0. simpl in H. symmetry in H. apply len_0 in H. symmetry. assumption.
   - intros. destruct H. induction v.
     + simpl in H. inversion H.
     + simpl in H. apply eq_add_S in H. simpl in H0. injection H0. intros. symmetry in H2.
        subst. assert (|u| = |v| -> u ++ (cons l v) = v ++ (cons l u)). 
        * intro. assumption.
        * apply case_egal1 in H2. f_equal. assert (|u|=|v| /\ u++v = v++u). split. assumption. assumption.
            specialize (IHu v H3). subst. reflexivity. assumption. assumption.
Qed.

Lemma three_cases :
  forall u v : word, |u| = |v| \/ |u| > |v| \/ |u| < |v|.
Proof.
  intros. apply cases_int.
Qed.

Lemma conc_egal_2 :
  forall u v v' : word, u++v = u++v' -> v=v'.
Proof.
  intro u. induction u.
  - intros. simpl in H. assumption.
  - intros. simpl in H. injection H. intro. apply IHu in H0. assumption.
Qed.

Lemma conc_pow1 : 
  forall (n m : nat) (u : word), u^n ++ u^m = u^(n+m).
Proof.
  intros. induction n. 
  - simpl. reflexivity.
  - simpl. rewrite <- conc_assoc. rewrite IHn. reflexivity.
Qed.

Lemma empty_or_larger :
  forall v : word, v=epsilon \/ |v|>0.
Proof.
  intro v. destruct v.
  - left. reflexivity.
  - right. simpl. apply int_strict_positive.
Qed.

Lemma pref_cut :
  forall v u :word, |u| > |v| /\ |v| > 0 /\ prefixe (|v|) u = v -> 
    exists u' : word, |u'| < |u| /\ u = v++u'.
Proof.
  intro. induction v.
  - intros. destruct H. destruct H0. inversion H0.
  - intro u. destruct u. 
    + intros. destruct H. simpl in H. inversion H.
    + intros. destruct H. destruct H0. inversion H1. subst. rewrite H4. assert (v=epsilon \/ |v|>0).
      apply empty_or_larger. case H2. 
      * intro. rewrite H3. simpl. exists u. split. apply succ_pos_strict. reflexivity.
      * intro. simpl. assert (|u| > |v| /\ |v| > 0 /\ prefixe (|v|) u = v). split.
        simpl in H. apply sup_succ_strict in H. assumption. split. assumption. assumption.
        specialize (IHv u H5). destruct IHv as [x H6]. exists x. destruct H6. apply lt_S in H6.
        split. assumption. f_equal. assumption.
Qed.

Lemma fine_wilf_aux :
  forall (k: nat) (u v : word), ((|u| + |v| <= k) /\ u++v = v++u) -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  intro k. induction k.
  - intros. destruct H. inversion H. exists v , 0, 0. simpl. apply zero_split in H2. destruct H2.
    apply len_0 in H1, H2. split. assumption. assumption.
  - intros u v. assert (|u| = |v| \/ |u| > |v| \/ |u| < |v|). apply three_cases. destruct H as [HA | [HB | HC]].
    + intros. destruct H. assert (|u| = |v| /\ u++v = v++u). split. assumption.
      assumption. apply case_egal in H1. exists u, 1, 1. split. simpl. rewrite <- conc_nil_l. reflexivity. simpl.
      rewrite <- conc_nil_l. symmetry. assumption.
    + intros. assert (v=epsilon \/ |v|>0). apply empty_or_larger. case H0.
      * intro. exists u, 0, 1. simpl. split. rewrite <- conc_nil_l. reflexivity. assumption.
      * intro. destruct H. apply gt_to_le in HB as HB_2. specialize (pref_inside_first (|v|) u v HB_2). intro. rewrite H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (|u| > |v| /\ |v| > 0 /\ prefixe (|v|) u = v).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [u' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (|u| + |v| <= S k /\ |u'| < |u|).
        split; assumption. specialize (remove_S_keep_o_n (|u|) (|v|) (|u'|) k H6). intro.
        assert (|u'| + |v| <= k /\ u'++v = v++u'). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_pow1 in H5.
        exists w, n, (n + m). split; assumption.
    + intros. assert (u=epsilon \/ |u|>0). apply empty_or_larger. case H0.
      * intro. exists v, 1, 0. simpl. split. assumption. rewrite <- conc_nil_l. reflexivity.
      * intro. destruct H. apply gt_to_le in HC as HC_2. specialize (pref_inside_first (|u|) v u HC_2). intro. rewrite <- H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (|v| > |u| /\ |u| > 0 /\ prefixe (|u|) v = u).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [v' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (|u| + |v| <= S k /\ |v'| < |v|).
        split; assumption. specialize (remove_S_keep_m_o (|u|) (|v|) (|v'|) k H6). intro.
        assert (|u| + |v'| <= k /\ u++v' = v'++u). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_pow1 in H5.
        exists w, (m + n), m. split; assumption.
Qed.

Theorem fine_wilf :
  forall (u v : word), u++v = v++u -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n.
Proof.
  intros. assert (forall k, ((|u| + |v| <= k) /\ u++v = v++u) -> 
  exists (w : word) (n m : nat), u = w^m /\ v = w^n). intro k. apply fine_wilf_aux.
  specialize (H0 (|u| + |v|)). assert (|u| + |v| <= |u| + |v|). apply le_n.
  assert (|u| + |v| <= |u| + |v| /\ u++v = v++u). split; assumption. apply H0 in H2.
  destruct H2 as [w [n [m H_egalites]]]. exists w, n, m. assumption.
Qed.

End Fine_Wilf.
