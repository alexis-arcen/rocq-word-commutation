# Documentation of the proof 

<details>
<summary>Here you can find the lemmas and definitions provided by our instructor.</summary>

```rocq
Section Fine_Wilf.

Fixpoint prefixe (k : nat) (u : mot) : mot :=
match k with
|0 => epsilon
|S k' => match u with
        |epsilon => epsilon
        |cons l u' => cons l (prefixe k' u')
        end
end.

Lemma pref_first_word :
  forall (u v : mot),  prefixe (long u) (conc u v) = u.
Proof.
Abort.

Lemma pref_inside_first :
  forall (k : nat) (u v : mot), k<=(long u) -> prefixe k (conc u v) = prefixe k u.
Proof.
Abort.

Lemma case_egal :
  forall (u v : mot), (long(u)=long(v) /\ conc u v = conc v u) -> u=v.
Proof.
Abort.

Lemma three_cases :
  forall u v : mot, long u = long v \/ long u > long v \/ long u < long v.
Proof.
Abort.

Lemma conc_egal_2 :
  forall u v v' : mot, conc u v = conc u v' -> v=v'.
Proof.
Abort.

Lemma conc_puiss :
  forall (n m : nat) (v x w : mot), 
    (v = puiss n w /\ x = puiss m w) -> conc v x = puiss (n+m) w.
Proof.
Abort.

Lemma empty_or_larger :
  forall v : mot, v=epsilon \/ long v>0.
Proof.
Abort.

Lemma pref_cut :
  forall v u :mot, long u > long v /\ long v > 0 /\ prefixe (long v) u = v -> 
    exists u' : mot, long u' < long u /\ u = conc v u'.
Proof.
Abort.

Lemma fine_wilf_aux :
  forall (k:nat) (u v : mot), ((long u + long v <= k) /\ conc u v = conc v u) -> 
  exists (w : mot) (n m :nat), u = (puiss m w) /\ v = (puiss n w).
Proof.
Abort.

Lemma fine_wilf :
  forall (u v : mot), conc u v = conc v u -> 
  exists (w : mot) (n m :nat), u = (puiss m w) /\ v = (puiss n w).
Proof.
Abort.

End Fine_Wilf.
