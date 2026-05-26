(* Still refining and translating the code. *)

Section Words.

Inductive letter : Type :=
| a : letter
| b : letter
| c : letter
| d : letter.

Inductive word : Type :=
| epsilon : word
| cons :letter -> word -> word.

Declare Scope word_scope.
Bind Scope word_scope with word.
Open Scope word_scope.

Fixpoint conc (u v : word) : word :=
match u with
| epsilon => v
| cons l u => cons l (conc u v)
end.

Notation "u ++ v" := (conc u v) : word_scope.

Lemma conc_nil_l :
  forall (u : word), u = u ++ epsilon.
Proof.
  intro. induction u.
  * simpl. reflexivity.
  * simpl. rewrite <- IHu. reflexivity.
Qed.

Lemma conc_assoc :
  forall (u v w : word), u ++ (v ++ w) = (u ++ v) ++ w.
Proof.
  intros. induction u.
  * simpl. reflexivity.
  * simpl. rewrite IHu. reflexivity.
Qed.

Fixpoint len (u : word) : nat :=
match u with
| epsilon => 0
| cons l u' => 1 + len u'
end.

Notation "| u |" := (len u) (at level 10) : word_scope.

Fixpoint pow (n : nat) (u : word) : word :=
match n with
| 0 => epsilon
| S n' => u ++ (pow n' u)
end.

Notation "u ^ n" := (pow n u) : word_scope.

Lemma len_0 :
  forall (u : word), |u| = 0 -> u = epsilon.
Proof.
  intro. induction u.
  * intro. reflexivity.
  * intro. simpl in H. discriminate.
Qed.

Fixpoint prefixe (k : nat) (u : word) : word :=
match k with
|0 => epsilon
|S k' => match u with
        |epsilon => epsilon
        |cons l u' => cons l (prefixe k' u')
        end
end.

Lemma pref_first_word :
  forall (u v : word),  prefixe (len u) (u ++ v) = u.
Proof.
  intros. induction u.
  - simpl. reflexivity.
  - simpl. rewrite IHu. reflexivity.
Qed.

End Words.

Section Arithmetics.

Lemma plus_commut :
  forall m n : nat, m+n=n+m.
Proof. 
  intros m n. induction m.
  - simpl. apply plus_n_O. 
  - simpl. rewrite <- plus_n_Sm. rewrite IHm. reflexivity.
Qed.

Lemma int_strict_positive :
  forall n : nat, S n > 0.
Proof.
  intro n. unfold gt. unfold lt. induction n.
  - apply le_n.
  - apply le_S in IHn. assumption.
Qed.

Lemma succ_pos_strict :
  forall n : nat, n < S n.
Proof.
  intro n. unfold lt. apply le_n.
Qed.

Lemma sup_succ_strict :
  forall m n : nat, S m > S n -> m > n.
Proof.
  intros m n H. unfold gt. unfold lt. unfold gt in H. unfold lt in H. apply le_S_n in H. assumption.
Qed.

Lemma le_disjunction :
  forall m n : nat, m <= n -> m = n \/ m < n.
Proof.
  intro m. induction m.
  - intro n. destruct n.
    + intro. left. reflexivity.
    + intro. right. assert (S n > 0). apply int_strict_positive. unfold gt in H0. assumption.
  - intro n. destruct n.
    + intro. inversion H.
    + intro. specialize (IHm n). apply le_S_n in H. apply IHm in H. case H.
      * intro. left. apply eq_S. assumption.
      * intro. right. unfold lt. unfold lt in H0. apply le_n_S in H0. assumption.
Qed.

Lemma cases_int :
  forall m n : nat, m = n \/ m > n \/ m < n.
Proof.
  intros m n. induction m.
  - destruct n.
    + left. reflexivity.
    + right. right. assert (S n > 0). apply int_strict_positive. unfold gt in H. assumption.
  - destruct IHm as [H0 | [H1 | H2]].
    + right. left. rewrite H0. unfold gt. apply succ_pos_strict.
    + right. left. unfold gt. unfold lt. unfold gt in H1. unfold lt in H1. apply le_S in H1. assumption.
    + unfold lt in H2. assert (S m <= n -> S m = n \/ S m < n). apply le_disjunction with (m := S m) (n := n).
      apply H in H2. case H2.
      * intro. left. assumption.
      * intro. right. right. assumption.
Qed.

End Arithmetics.

Section Fine_Wilf.

Notation "u ++ v" := (conc u v).

Lemma pref_inside_first :
  forall (k : nat) (u v : word), k<=(len u) -> prefixe k (u ++ v) = prefixe k u.
Proof.
  intro k. induction k.
  * intros. simpl. reflexivity.
  * intro u. intro v. induction u.
    ** intros. simpl in H. inversion H.
    ** intros. simpl in H. apply le_S_n in H. specialize (IHk u v H). 
       simpl. rewrite IHk. reflexivity.
Qed.

Lemma case_egal11 : 
  forall (u v w1 w2 : word), len u = len v -> u ++ w1 = v ++ w2 -> u = v.
Proof.
  intro u. induction u.
  - intros. simpl in H. symmetry in H. apply len_0 in H. symmetry. assumption.
  - intro v. destruct v. 
    + intros. simpl in H. inversion H.
    + intros. simpl in H. injection H. intro. simpl in H0. injection H0. intros. symmetry in H3.
      subst. f_equal. apply IHu with (w1:=w1) (w2:=w2). assumption. assumption.
Qed.

Lemma case_egal1 :
forall (u v : word) (l : letter), len u = len v -> u ++ (cons l v) = v ++ (cons l u) -> u++v = v++u.
Proof.
  intros. assert (u=v).
  apply case_egal11 with (w1 := cons l v) (w2 := cons l u). assumption. assumption.
  rewrite H1. reflexivity.
Qed.

Lemma case_egal :
  forall (u v : word), (len(u)=len(v) /\ u++v = v++u) -> u=v.
Proof.
  intro u. induction u.
   - intros. destruct H. simpl in H0. simpl in H. symmetry in H. apply len_0 in H. symmetry. assumption.
   - intros. destruct H. induction v.
     + simpl in H. inversion H.
     + simpl in H. apply eq_add_S in H. simpl in H0. injection H0. intros. symmetry in H2.
        subst. assert (len u = len v -> u ++ (cons l v) = v ++ (cons l u)). 
        * intro. assumption.
        * apply case_egal1 in H2. f_equal. assert (len(u)=len(v) /\ u++v = v++u). split. assumption. assumption.
            specialize (IHu v H3). subst. reflexivity. assumption. assumption.
Qed.

Lemma three_cases :
  forall u v : word, len u = len v \/ len u > len v \/ len u < len v.
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
  forall (n m : nat) (u : word), (pow n u) ++ (pow m u) = pow (n+m) u.
Proof.
  intros. induction n. 
  * simpl. reflexivity.
  * simpl. rewrite <- conc_assoc. rewrite IHn. reflexivity.
Qed.

Lemma conc_pow :
  forall (n m : nat) (v x w : word), 
    (v = pow n w /\ x = pow m w) -> v++x = pow (n+m) w.
Proof.
  intro n. destruct n.
  - intros. destruct H. simpl in H. rewrite H. simpl. assumption.
  - intros. destruct H. rewrite H0. rewrite H. apply conc_pow1.
Qed.

Lemma empty_or_larger :
  forall v : word, v=epsilon \/ len v>0.
Proof.
  intro v. destruct v.
  - left. reflexivity.
  - right. simpl. apply int_strict_positive.
Qed.

Lemma lt_S :
  forall n m, n < m -> n < S m.
Proof. 
  intros n m. intro. unfold lt in H. unfold lt. apply le_S in H. assumption.
Qed.

Lemma pref_cut :
  forall v u :word, len u > len v /\ len v > 0 /\ prefixe (len v) u = v -> 
    exists u' : word, len u' < len u /\ u = v++u'.
Proof.
  intro. induction v.
  - intros. destruct H. destruct H0. inversion H0.
  - intro u. destruct u. 
    + intros. destruct H. simpl in H. inversion H.
    + intros. destruct H. destruct H0. inversion H1. subst. rewrite H4. assert (v=epsilon \/ len v>0).
      apply empty_or_larger. case H2. 
      * intro. rewrite H3. simpl. exists u. split. apply succ_pos_strict. reflexivity.
      * intro. simpl. assert (len u > len v /\ len v > 0 /\ prefixe (len v) u = v). split.
        simpl in H. apply sup_succ_strict in H. assumption. split. assumption. assumption.
        specialize (IHv u H5). destruct IHv as [x H6]. exists x. destruct H6. apply lt_S in H6.
        split. assumption. f_equal. assumption.
Qed.

Lemma zero_split :
  forall m n, m+n=0 -> m=0 /\ n=0.
Proof. 
  intros m n. destruct m.
  - intros. split. reflexivity. assumption.
  - intro. simpl in H. inversion H.
Qed.

Lemma gt_to_le :
  forall m n, n > m -> m <= n.
Proof. 
  intros. unfold gt in H. unfold lt in H. apply le_S_n. apply le_S. assumption.
Qed.

Lemma lt_add_succ_both_sides :
  forall m n, m < n -> S m < S n.
Proof.
  intros m n H. unfold lt in H. unfold lt. apply le_n_S. assumption.
Qed.

Lemma add_zero_idemp_r  :
  forall m, m + 0 = m.
Proof.
  intro m. induction m.
  - reflexivity.
  - apply eq_S in IHm. rewrite plus_Sn_m. assumption.
Qed.

Lemma lt_add_n_both_sides :
  forall o m n, o < m -> o+n < m+n.
Proof.
  intros o m n.
  induction n.
  - intro. simpl. rewrite add_zero_idemp_r . rewrite add_zero_idemp_r . assumption.
  - intro. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply lt_add_succ_both_sides. apply IHn. assumption.
Qed.

Lemma lt_le_trans  :
  forall a b c, a < b /\ b <= c -> a < c.
Proof.
  unfold lt. intros a b c. intro. destruct H. induction H0.
  - assumption.
  - apply le_S. assumption.
Qed.

Lemma remove_succ_keep_o_n :
  forall m n o k, m + n <= S k /\ o < m -> o + n <= k.
Proof. 
  intros m n o k H. destruct H. apply lt_add_n_both_sides with (o:=o) (m:=m) (n:=n) in H0.
  assert (o + n < m + n /\ m + n <= S k). split; assumption. apply lt_le_trans  in H1. unfold lt in H1.
  apply le_S_n in H1. assumption.
Qed.

Lemma remove_succ_keep_m_o :
  forall m n o k, m + n <= S k /\ o < n -> m + o <= k.
Proof. 
  intros m n o k H. destruct H. assert (o + m < n + m). apply lt_add_n_both_sides. assumption.
  replace (m+n) with (n+m) in H. assert (o + m < n + m /\ n + m <= S k). split; assumption. apply lt_le_trans  in H2.
  apply le_S_n in H2. replace (m+o) with (o+m). assumption. apply plus_commut. apply plus_commut.
Qed.

Lemma fine_wilf_aux :
  forall (k: nat) (u v : word), ((len u + len v <= k) /\ u++v = v++u) -> 
  exists (w : word) (n m : nat), u = (pow m w) /\ v = (pow n w).
Proof.
  intro k. induction k.
  - intros. destruct H. inversion H. exists v , 0, 0. simpl. apply zero_split in H2. destruct H2.
    apply len_0 in H1, H2. split. assumption. assumption.
  - intros u v. assert (len u = len v \/ len u > len v \/ len u < len v). apply three_cases. destruct H as [HA | [HB | HC]].
    + intros. destruct H. assert (len u = len v /\ u++v = v++u). split. assumption.
      assumption. apply case_egal in H1. exists u, 1, 1. split. simpl. rewrite <- conc_nil_l. reflexivity. simpl.
      rewrite <- conc_nil_l. symmetry. assumption.
    + intros. assert (v=epsilon \/ len v>0). apply empty_or_larger. case H0.
      * intro. exists u, 0, 1. simpl. split. rewrite <- conc_nil_l. reflexivity. assumption.
      * intro. destruct H. apply gt_to_le in HB as HB_2. specialize (pref_inside_first (len v) u v HB_2). intro. rewrite H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (len u > len v /\ len v > 0 /\ prefixe (len v) u = v).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [u' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (len u + len v <= S k /\ len u' < len u).
        split; assumption. specialize (remove_succ_keep_o_n (len u) (len v) (len u') k H6). intro.
        assert (len u' + len v <= k /\ u'++v = v++u'). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_pow1 in H5.
        exists w, n, (n + m). split; assumption.
    + intros. assert (u=epsilon \/ len u>0). apply empty_or_larger. case H0.
      * intro. exists v, 1, 0. simpl. split. assumption. rewrite <- conc_nil_l. reflexivity.
      * intro. destruct H. apply gt_to_le in HC as HC_2. specialize (pref_inside_first (len u) v u HC_2). intro. rewrite <- H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (len v > len u /\ len u > 0 /\ prefixe (len u) v = u).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [v' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (len u + len v <= S k /\ len v' < len v).
        split; assumption. specialize (remove_succ_keep_m_o (len u) (len v) (len v') k H6). intro.
        assert (len u + len v' <= k /\ u++v' = v'++u). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_pow1 in H5.
        exists w, (m + n), m. split; assumption.
Qed.

Lemma fine_wilf :
  forall (u v : word), u++v = v++u -> 
  exists (w : word) (n m : nat), u = (pow m w) /\ v = (pow n w).
Proof.
  intros. assert (forall k, ((len u + len v <= k) /\ u++v = v++u) -> 
  exists (w : word) (n m : nat), u = (pow m w) /\ v = (pow n w)). intro k. apply fine_wilf_aux.
  specialize (H0 (len u + len v)). assert (len u + len v <= len u + len v). apply le_n.
  assert (len u + len v <= len u + len v /\ u++v = v++u). split; assumption. apply H0 in H2.
  destruct H2 as [w [n [m H_egalites]]]. exists w, n, m. assumption.
Qed.

End Fine_Wilf.
