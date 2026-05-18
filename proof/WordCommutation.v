(* Still refining and translating the code. *)

Section Words.

Inductive lettre : Type :=
| a : lettre
| b : lettre
| c : lettre
| d : lettre.

Inductive mot : Type :=
| epsilon : mot
| cons :lettre -> mot -> mot.

Fixpoint conc (u v:mot) : mot :=
match u with
| epsilon => v
| cons l u => cons l (conc u v)
end.

Lemma conc_nil_l :
  forall (u:mot), u = conc u epsilon.
Proof.
  intro. induction u.
  * simpl. reflexivity.
  * simpl. rewrite <- IHu. reflexivity.
Qed.

Lemma conc_assoc :
  forall (u v w:mot), conc u (conc v w) = conc (conc u v) w.
Proof.
  intros. induction u.
  * simpl. reflexivity.
  * simpl. rewrite IHu. reflexivity.
Qed.

Fixpoint long (u:mot) : nat :=
match u with
| epsilon => 0
| cons l u => 1 + long u
end.

Fixpoint puiss (n:nat) (u:mot) : mot :=
match n with
| 0 => epsilon
| S n => conc u (puiss n u)
end.

Theorem long_0 :
  forall (u:mot), long u = 0 -> u = epsilon.
Proof.
  intro. induction u.
  * intro. reflexivity.
  * intro. simpl in H. discriminate.
Qed.

Fixpoint prefixe (k : nat) (u : mot) : mot :=
match k with
|0 => epsilon
|S k' => match u with
        |epsilon => epsilon
        |cons l u' => cons l (prefixe k' u')
        end
end.

Lemma pref_max :
  forall u : mot, prefixe (long u) u = u.
Proof.
  intro. induction u.
  - simpl. reflexivity.
  - simpl. rewrite IHu. reflexivity.
Qed.

Lemma pref_first_word :
  forall (u v : mot),  prefixe (long u) (conc u v) = u.
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

Lemma inf_refl :
  forall n : nat, n <= n.
Proof.
  intro n. apply le_n.
Qed.

Lemma egal_succ :
  forall n m : nat, S n = S m -> n=m.
Proof.
  intros n m. apply eq_add_S.
Qed.

Lemma int_strict_positive :
  forall n : nat, S n > 0.
Proof.
  intro n. unfold gt. unfold lt. induction n.
  - apply inf_refl.
  - apply le_S in IHn. assumption.
Qed.

Lemma succ_pos_strict :
  forall n : nat, n < S n.
Proof.
  intro n. unfold lt. apply inf_refl.
Qed.

Lemma inf_succ :
  forall n m : nat, S n <= S m -> n<=m.
Proof.
  apply le_S_n.
Qed.

Lemma sup_succ_strict :
  forall m n : nat, S m > S n -> m > n.
Proof.
  intros m n H. unfold gt. unfold lt. unfold gt in H. unfold lt in H. apply inf_succ in H. assumption.
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
    + intro. specialize (IHm n). apply inf_succ in H. apply IHm in H. case H.
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

Lemma pref_inside_first :
  forall (k : nat) (u v : mot), k<=(long u) -> prefixe k (conc u v) = prefixe k u.
Proof.
  intro k. induction k.
  * intros. simpl. reflexivity.
  * intro u. intro v. induction u.
    ** intros. simpl in H. inversion H.
    ** intros. simpl in H. apply inf_succ in H. specialize (IHk u v H). 
       simpl. rewrite IHk. reflexivity.
Qed.

Lemma case_egal11 : 
  forall (u v w1 w2 : mot), long u = long v -> conc u w1 = conc v w2 -> u = v.
Proof.
  intro u. induction u.
  - intros. simpl in H. symmetry in H. apply long_0 in H. symmetry. assumption.
  - intro v. destruct v. 
    + intros. simpl in H. inversion H.
    + intros. simpl in H. injection H. intro. simpl in H0. injection H0. intros. symmetry in H3.
      subst. f_equal. apply IHu with (w1:=w1) (w2:=w2). assumption. assumption.
Qed.

Lemma case_egal1 :
forall (u v : mot) (l : lettre), long u = long v -> conc u (cons l v) = conc v (cons l u) -> conc u v = conc v u.
Proof.
  intros. assert (u=v).
  apply case_egal11 with (w1 := cons l v) (w2 := cons l u). assumption. assumption.
  rewrite H1. reflexivity.
Qed.

Lemma case_egal :
  forall (u v : mot), (long(u)=long(v) /\ conc u v = conc v u) -> u=v.
Proof.
  intro u. induction u.
   - intros. destruct H. simpl in H0. simpl in H. symmetry in H. apply long_0 in H. symmetry. assumption.
   - intros. destruct H. induction v.
     + simpl in H. inversion H.
     + simpl in H. apply egal_succ in H. simpl in H0. injection H0. intros. symmetry in H2.
        subst. assert (long u = long v -> conc u (cons l v) = conc v (cons l u)). 
        * intro. assumption.
        * apply case_egal1 in H2. f_equal. assert (long(u)=long(v) /\ conc u v = conc v u). split. assumption. assumption.
            specialize (IHu v H3). subst. reflexivity. assumption. assumption.
Qed.

Lemma three_cases :
  forall u v : mot, long u = long v \/ long u > long v \/ long u < long v.
Proof.
  intros. apply cases_int.
Qed.

Lemma puiss_1 :
  forall (u : mot), u = puiss 1 u. 
Proof.
  intro. simpl. apply conc_nil_l.
Qed.

Lemma conc_idem : 
  forall u v v' : mot, v=v' -> conc u v = conc u v'.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma conc_egal_2 :
  forall u v v' : mot, conc u v = conc u v' -> v=v'.
Proof.
  intro u. induction u.
  - intros. simpl in H. assumption.
  - intros. simpl in H. injection H. intro. apply IHu in H0. assumption.
Qed.

Lemma conc_puiss1 : 
  forall (n m : nat) (u : mot), conc (puiss n u) (puiss m u) = puiss (n+m) u.
Proof.
  intros. induction n. 
  * simpl. reflexivity.
  * simpl. rewrite <- conc_assoc. rewrite IHn. reflexivity.
Qed.

Lemma conc_puiss :
  forall (n m : nat) (v x w : mot), 
    (v = puiss n w /\ x = puiss m w) -> conc v x = puiss (n+m) w.
Proof.
  intro n. destruct n.
  - intros. destruct H. simpl in H. rewrite H. simpl. assumption.
  - intros. destruct H. rewrite H0. rewrite H. apply conc_puiss1.
Qed.

Lemma empty_or_larger :
  forall v : mot, v=epsilon \/ long v>0.
Proof.
  intro v. destruct v.
  - left. reflexivity.
  - right. simpl. apply int_strict_positive.
Qed.

Lemma pref_cut1 :
  forall n m, n < m -> n < S m.
Proof. 
  intros n m. intro. unfold lt in H. unfold lt. apply le_S in H. assumption.
Qed.

Lemma pref_cut :
  forall v u :mot, long u > long v /\ long v > 0 /\ prefixe (long v) u = v -> 
    exists u' : mot, long u' < long u /\ u = conc v u'.
Proof.
  intro. induction v.
  - intros. destruct H. destruct H0. inversion H0.
  - intro u. destruct u. 
    + intros. destruct H. simpl in H. inversion H.
    + intros. destruct H. destruct H0. inversion H1. subst. rewrite H4. assert (v=epsilon \/ long v>0).
      apply empty_or_larger. case H2. 
      * intro. rewrite H3. simpl. exists u. split. apply succ_pos_strict. reflexivity.
      * intro. simpl. assert (long u > long v /\ long v > 0 /\ prefixe (long v) u = v). split.
        simpl in H. apply sup_succ_strict in H. assumption. split. assumption. assumption.
        specialize (IHv u H5). destruct IHv as [x H6]. exists x. destruct H6. apply pref_cut1 in H6.
        split. assumption. f_equal. assumption.
Qed.

Lemma fine_wilf_aux1 :
  forall m n, m+n=0 -> m=0 /\ n=0.
Proof. 
  intros m n. destruct m.
  - intros. split. reflexivity. assumption.
  - intro. simpl in H. inversion H.
Qed.

Lemma fine_wilf_aux2 :
  forall m n, n > m -> m <= n.
Proof. 
  intros. unfold gt in H. unfold lt in H. apply le_S_n. apply le_S. assumption.
Qed.

Lemma fine_wilf_aux311 :
  forall m n, m < n -> S m < S n.
Proof.
  intros m n H. unfold lt in H. unfold lt. apply le_n_S. assumption.
Qed.

Lemma fine_wilf_aux312 :
  forall m, m + 0 = m.
Proof.
  intro m. induction m.
  - reflexivity.
  - apply eq_S in IHm. rewrite plus_Sn_m. assumption.
Qed.

Lemma fine_wilf_aux31 :
  forall o m n, o < m -> o+n < m+n.
Proof.
  intros o m n.
  induction n.
  - intro. simpl. rewrite fine_wilf_aux312. rewrite fine_wilf_aux312. assumption.
  - intro. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply fine_wilf_aux311. apply IHn. assumption.
Qed.

Lemma fine_wilf_aux32 :
  forall a b c, a < b /\ b <= c -> a < c.
Proof.
  unfold lt. intros a b c. intro. destruct H. induction H0.
  - assumption.
  - apply le_S. assumption.
Qed.

Lemma fine_wilf_aux3 :
  forall m n o k, m + n <= S k /\ o < m -> o + n <= k.
Proof. 
  intros m n o k H. destruct H. apply fine_wilf_aux31 with (o:=o) (m:=m) (n:=n) in H0.
  assert (o + n < m + n /\ m + n <= S k). split; assumption. apply fine_wilf_aux32 in H1. unfold lt in H1.
  apply le_S_n in H1. assumption.
Qed.

Lemma fine_wilf_aux4 :
  forall m n o k, m + n <= S k /\ o < n -> m + o <= k.
Proof. 
  intros m n o k H. destruct H. assert (o + m < n + m). apply fine_wilf_aux31. assumption.
  replace (m+n) with (n+m) in H. assert (o + m < n + m /\ n + m <= S k). split; assumption. apply fine_wilf_aux32 in H2.
  apply le_S_n in H2. replace (m+o) with (o+m). assumption. apply plus_commut. apply plus_commut.
Qed.

Lemma fine_wilf_aux :
  forall (k: nat) (u v : mot), ((long u + long v <= k) /\ conc u v = conc v u) -> 
  exists (w : mot) (n m : nat), u = (puiss m w) /\ v = (puiss n w).
Proof.
  intro k. induction k.
  - intros. destruct H. inversion H. exists v , 0, 0. simpl. apply fine_wilf_aux1 in H2. destruct H2.
    apply long_0 in H1, H2. split. assumption. assumption.
  - intros u v. assert (long u = long v \/ long u > long v \/ long u < long v). apply three_cases. destruct H as [HA | [HB | HC]].
    + intros. destruct H. assert (long u = long v /\ conc u v = conc v u). split. assumption.
      assumption. apply case_egal in H1. exists u, 1, 1. split. simpl. rewrite <- conc_nil_l. reflexivity. simpl.
      rewrite <- conc_nil_l. symmetry. assumption.
    + intros. assert (v=epsilon \/ long v>0). apply empty_or_larger. case H0.
      * intro. exists u, 0, 1. simpl. split. rewrite <- conc_nil_l. reflexivity. assumption.
      * intro. destruct H. apply fine_wilf_aux2 in HB as HB_2. specialize (pref_inside_first (long v) u v HB_2). intro. rewrite H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (long u > long v /\ long v > 0 /\ prefixe (long v) u = v).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [u' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (long u + long v <= S k /\ long u' < long u).
        split; assumption. specialize (fine_wilf_aux3 (long u) (long v) (long u') k H6). intro.
        assert (long u' + long v <= k /\ conc u' v = conc v u'). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_puiss1 in H5.
        exists w, n, (n + m). split; assumption.
    + intros. assert (u=epsilon \/ long u>0). apply empty_or_larger. case H0.
      * intro. exists v, 1, 0. simpl. split. assumption. rewrite <- conc_nil_l. reflexivity.
      * intro. destruct H. apply fine_wilf_aux2 in HC as HC_2. specialize (pref_inside_first (long u) v u HC_2). intro. rewrite <- H2 in H3.
        rewrite pref_first_word in H3. symmetry in H3. assert (long v > long u /\ long u > 0 /\ prefixe (long u) v = u).
        repeat split; assumption. apply pref_cut in H4. destruct H4 as [v' H4]. destruct H4.
        rewrite H5 in H2. rewrite <- conc_assoc in H2. apply conc_egal_2 in H2. assert (long u + long v <= S k /\ long v' < long v).
        split; assumption. specialize (fine_wilf_aux4 (long u) (long v) (long v') k H6). intro.
        assert (long u + long v' <= k /\ conc u v' = conc v' u). split; assumption. apply IHk in H8.
        destruct H8 as [w [n [m H8]]]. destruct H8. rewrite H8 in H5. rewrite H9 in H5. rewrite conc_puiss1 in H5.
        exists w, (m + n), m. split; assumption.
Qed.

Lemma fine_wilf :
  forall (u v : mot), conc u v = conc v u -> 
  exists (w : mot) (n m : nat), u = (puiss m w) /\ v = (puiss n w).
Proof.
  intros. assert (forall k, ((long u + long v <= k) /\ conc u v = conc v u) -> 
  exists (w : mot) (n m : nat), u = (puiss m w) /\ v = (puiss n w)). intro k. apply fine_wilf_aux.
  specialize (H0 (long u + long v)). assert (long u + long v <= long u + long v). apply inf_refl.
  assert (long u + long v <= long u + long v /\ conc u v = conc v u). split; assumption. apply H0 in H2.
  destruct H2 as [w [n [m H_egalites]]]. exists w, n, m. assumption.
Qed.

End Fine_Wilf.