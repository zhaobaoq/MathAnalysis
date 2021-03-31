Require Export A_12_1.

Module A12_2.

(* 等比级数 *)

(* 首项为a，公比为q的数列 *)
Theorem IsProportionalSequence : ∀ (a q : R),
  IsSeq {` λ m v, v = a * (pow q m) `}.
Proof.
  intros a q. split.
  - unfold Function. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption.
  - apply AxiomI. intro m; split; intro I1; apply AxiomII;
    applyAxiomII I1; auto. exists (a * (pow q m)).
    apply AxiomII'. reflexivity.
Qed.

(* 等比数列前n项和 *)
Theorem SumProportionalSequence : ∀ (a q : R) (n : nat),
  q <> 1 -> Σ {` λ m v, v = a * q^^m `} n
  = a * (1 - q^^(S n)) / (1 - q).
Proof.
  intros a q n H0.
  generalize (IsProportionalSequence a q). intros [H1 H2].
  assert (H3 : ∀ m, {` λ m v, v = a * (pow q m) `} [m]
    = a * (pow q m)).
  { intro m. apply f_x; auto. apply AxiomII'. reflexivity. }
  induction n as [|n IHn].
  - simpl. rewrite H3. simpl. field. lra.
  - simpl. rewrite IHn. rewrite H3. simpl. field. lra.
Qed.

Lemma Lemma12_2_0 : ∀ q n, 1 < q -> (q - 1) * (INR n) < q^^n.
Proof.
  intros q n H0. induction n as [|n IHn].
  - simpl. lra.
  - rewrite S_INR. simpl. rewrite Rmult_plus_distr_l.
    assert (H1 : q = 1 + (q - 1)). field. pattern q at 3.
    rewrite H1. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
    rewrite Rmult_1_r. apply Rplus_lt_le_compat; auto.
    assert (H2 : q - 1 = (q - 1) * 1). field.
    pattern (q - 1) at 1. rewrite H2.
    assert (H3 : 0 <= q - 1). lra.
    apply Rmult_le_compat_l; auto.
    assert (H4 : ∀ m, 1 <= pow q m).
    { intro m. induction m as [|m IHm].
      - simpl. right. reflexivity.
      - simpl. apply Rmult_le_compat_l with (r := q) in IHm; lra. }
    apply H4.
Qed.

(* 等比级数收敛于 a / (1 - q) *)
Theorem SeriesProportionalSequence : ∀ (a q : R),
  -1 < q < 1 -> limit_seq (Series {` λ m v, v = a * q^^m `})
  (a / (1 - q)).
Proof.
  intros a q H0. generalize (IsProportionalSequence a q). intro H1.
  generalize (SeriesSeq {` λ m v, v = a * q ^^ m `}); intros H3.
  destruct H1 as [H1 H2].
  split; auto. intros ε H4.
  destruct classic with (P := (q = 0)) as [H5 | H5].
  - rewrite H5 in *. exists (0%nat). intros m H6.
    unfold ConSer. rewrite SeriesValue.
    assert (H7 : ∀ k, Abs[Σ {` λ m v, v = a * (pow 0 m) `} k -
      a / (1 - 0)] < ε).
    { intro k. induction k as [|k IHk].
      - simpl. assert (I1 : {` λ m v, v = a * (pow 0 m) `}[0%nat] = a).
        { apply f_x; auto. apply AxiomII'. simpl. field. }
        rewrite I1. assert (I2 : a - a / (1 - 0) = 0). field.
        rewrite I2. rewrite Abs_ge; lra.
      - simpl. assert (I1 : {` λ m v, v = a * (pow 0 m) `}[S k] = 0).
        { apply f_x; auto. apply AxiomII'. simpl. field. }
        rewrite I1.
        assert (I2 : Σ {` λ m v, v = a * (pow 0 m) `} k +
          0 - a / (1 - 0) = Σ {` λ m v, v = a * (pow 0 m) `} k
          - a / (1 - 0)). field.
        rewrite I2. assumption. }
    apply H7.
  - destruct classic with (P := (a = 0)) as [H6 | H6].
    + rewrite H6 in *. exists (0%nat). intros m H7.
      unfold ConSer. rewrite SeriesValue.
      assert (H8 : ∀ k, Σ {` λ m v, v = 0 * (pow q m) `} k = 0).
      { intro k. induction k as [|k IHk].
        - simpl. assert (I1 : {` λ m v, v = 0 * (pow q m) `}[0%nat] = 0).
          { apply f_x; auto. apply AxiomII'. field. }
          rewrite I1. reflexivity.
        - simpl. assert (I1 : {` λ m v, v = 0 * (pow q m) `}[S k] = 0).
          { apply f_x; auto. apply AxiomII'. field. }
          rewrite I1. rewrite IHk. field. }
      rewrite (H8 m). assert (H9 : 0 - 0 / (1 - q) = 0). field. lra.
      rewrite H9. rewrite Abs_ge; lra.
    + assert (H7 : 0 < Abs[q] < 1).
      { apply Rdichotomy in H5. destruct H5 as [H5 | H5].
        - rewrite Abs_lt; auto. lra.
        - rewrite Abs_gt; auto. lra. }
      apply Abs_not_eq_0 in H6 as H8.
      assert (H9 : 0 < (/Abs[a]) * ((/Abs[q]) - 1)).
      { apply Rmult_lt_0_compat.
        - apply Rinv_0_lt_compat. assumption.
        - destruct H7 as [H7 H9].
          apply Rinv_lt_contravar in H9 as H11; lra. }
      assert (H10 : 0 < /(ε * (1 - q))).
      { apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; lra. }
      generalize (Archimedes ((/Abs[a]) * ((/Abs[q]) - 1))
          (/(ε * (1 - q))) H9 H10). intros [N H11].
      exists N. intros m H12.
      unfold ConSer. rewrite SeriesValue.
      rewrite SumProportionalSequence; try lra.
      assert (H13 : a * (1 - pow q (S m)) / (1 - q)
        - a / (1 - q) = - (a * (pow q (S m)) / (1 - q))). field; lra.
      rewrite H13. clear H13. rewrite <- Abs_eq_neg.
      assert (H13 : 1 - q > 0). lra.
      rewrite Abs_div; try lra. rewrite (Abs_gt (1 - q)); auto.
      apply Rmult_lt_reg_r with (r := 1 - q); auto.
      assert (H14 : Abs [a * pow q (S m)]
        / (1 - q) * (1 - q) = Abs [a * pow q (S m)]). field; try lra.
      rewrite H14. clear H14. rewrite Abs_mult.
      assert (H14 : ∀ k, pow q k <> 0).
      { intro k. induction k as [|k IHk].
        - simpl. lra.
        - simpl. apply Rmult_integral_contrapositive_currified; auto. }
      assert (H15 : 0 < Abs [pow q (S m)]).
      { apply Abs_not_eq_0. apply H14. }
      assert (H16 : Abs [a] * Abs [pow q (S m)] <> 0).
      { apply Rmult_integral_contrapositive_currified; 
        apply Rgt_not_eq; assumption. }
      rewrite <- (Rinv_involutive (Abs [a] * Abs [pow q (S m)])); auto.
      assert (H17 : ε * (1 - q) <> 0).
      { apply Rmult_integral_contrapositive_currified;
        apply Rgt_not_eq; assumption. }
      rewrite <- Rinv_involutive; auto.
      assert (H18 : 0 < / (ε * (1 - q))
        * / (Abs [a] * Abs [pow q (S m)])).
      { apply Rmult_lt_0_compat; auto.
        apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; auto. }
      apply Rinv_lt_contravar; auto.
      rewrite (Rinv_mult_distr (Abs[a]) (Abs[pow q (S m)])); try lra.
      assert (H19 : ∀ k, /(Abs[pow q k]) = pow (/Abs[q]) k).
      { intro k. induction k as [|k IHk].
        - simpl. rewrite Abs_gt; lra.
        - simpl. rewrite Abs_mult. rewrite Rinv_mult_distr; try lra.
          + rewrite IHk. reflexivity.
          + generalize (H14 k). intro I1. apply Abs_not_eq_0 in I1.
            lra. }
      rewrite H19. assert (H20 : 1 < /Abs[q]).
      { apply Rdichotomy in H5. destruct H5 as [I1 | I1].
        - rewrite Abs_lt; auto. rewrite <- Rinv_1.
          apply Rinv_lt_contravar; lra.
        - rewrite Abs_gt; auto. rewrite <- Rinv_1.
          apply Rinv_lt_contravar; lra. }
      generalize (Lemma12_2_0 (/Abs[q]) (S m) H20). intro H21.
      assert (H22 : 0 < / Abs [a]).
      { apply Rinv_0_lt_compat. assumption. }
      apply Rmult_lt_compat_l with (r := (/ Abs [a])) in H21; auto.
      apply Rlt_trans with (r2 :=
        / Abs [a] * ((/ Abs [q] - 1) * INR (S m))); auto.
      assert (H23 : INR N * (/ Abs [a] * (/ Abs [q] - 1))
        < / Abs [a] * ((/ Abs [q] - 1) * INR (S m))).
      { rewrite Rmult_comm. rewrite <- Rmult_assoc.
        apply Rmult_lt_compat_l.
        - apply Rmult_lt_0_compat; lra.
        - apply lt_INR. apply Nat.lt_lt_succ_r. assumption. }
      lra.
Qed.

(* 定义：正项级数 *)
Definition PosSer (u : Seq) := ∀ n, 0 <= u[n].

Theorem Theorem12_5 : ∀ (u : Seq), PosSer u
    -> (ConSer u <-> (BoundedSeq (Series u))).
Proof.
  intros u H1. split; intro H2.
  - split; try apply SeriesSeq; auto.
    apply Theorem2_3'. assumption.
  - apply Theorem2_9; auto. unfold MonotonicSeq. left.
    unfold IncreaseSeq. split; try apply SeriesSeq; auto.
    intro n. rewrite SeriesValue; auto. rewrite SeriesValue; auto.
    simpl. generalize (H1 (S n)). intro H3.
    apply Rplus_le_compat_l with (r := Σ u n) in H3.
    rewrite Rplus_0_r in H3. assumption.
Qed.

(* 定理2: 比较原则 *)
Theorem Theorem12_6' : ∀ (u v : Seq), PosSer u
  -> PosSer v -> (∀ n, u[n] <= v[n]) ->
  ConSer v -> ConSer u.
Proof.
  intros u v H2 H3 H4 H5.
  apply Theorem12_5 in H5 as H6; auto.
  unfold BoundedSeq in H6. destruct H6 as [H6 [M H7]].
  assert (H8 : ∀ n, 0 <= (Series v) [n]).
  { intro n. rewrite SeriesValue; auto.
    induction n as [|n IHn].
    - simpl. apply H3.
    - simpl. apply Rplus_le_le_0_compat; auto. }
  assert (H9 : ∀ n, 0 <= (Series u) [n]).
  { intro n. rewrite SeriesValue; auto.
    induction n as [|n IHn].
    - simpl. apply H2.
    - simpl. apply Rplus_le_le_0_compat; auto. }
  assert (H10 : ∀ n, Σ u n <= Σ v n).
  { intro n. induction n as [|n IHn].
    - simpl. apply H4.
    - simpl. apply Rplus_le_compat; auto. }
  apply Theorem12_5; auto. split.
  - apply SeriesSeq.
  - exists M. intro n. generalize (H9 n). intro H11.
    apply Rle_ge in H11. rewrite Abs_ge; auto.
    rewrite SeriesValue; auto.
    apply Rle_trans with (r2 := Σ v n); auto.
    generalize (H7 n). intro H12. generalize (H8 n). intro H13.
    apply Rle_ge in H13. rewrite Abs_ge in H12; auto.
    rewrite SeriesValue in H12; auto.
Qed.

Theorem Theorem12_6'' : ∀ (u v : Seq),
  IsSeq u -> IsSeq v -> PosSer u -> PosSer v
  -> (∃ N k, (k > 0) /\ (∀ n, (N <= n)%nat -> u[n] <= k * v[n]))
  -> ConSer v -> ConSer u.
Proof.
  intros u v H0 H1 H2 H3 [N [k [H5 H6]]] H4.
  assert (H7 : ∃ u', u' = {` λ n x, x = u[(n + N)%nat] `}).
  { exists {` λ n x, x = u[(n + N)%nat] `}; reflexivity. }
  destruct H7 as [u' H7].
  assert (H8 : ∃ v', v' = {` λ n x, x = k * v[(n + N)%nat] `}).
  { exists {` λ n x, x = k * v[(n + N)%nat] `}; reflexivity. }
  destruct H8 as [v' H8].
  apply Theorem12_3 with (M := N); auto. rewrite <- H7.
  assert (H9 : IsSeq u').
  { rewrite H7. split.
    - unfold Function. intros x y z I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption.
    - apply AxiomI. intro n; split; intro I1; apply AxiomII; auto.
      exists (u[(n + N)%nat]). apply AxiomII'.
      reflexivity. }
  assert (H10 : IsSeq v').
  { rewrite H8. split.
    - unfold Function. intros x y z I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption.
    - apply AxiomI. intro n; split; intro I1; apply AxiomII; auto.
      exists (k * v[(n + N)%nat]). apply AxiomII'.
      reflexivity. }
  assert (H11 : ∀ n, u'[n] = u[(n + N)%nat]).
  { intro n. apply f_x; try apply H9. rewrite H7. apply AxiomII'.
    reflexivity. }
  assert (H12 : ∀ n, v'[n] = k * v[(n + N)%nat]).
  { intro n. apply f_x; try apply H10. rewrite H8. apply AxiomII'.
    reflexivity. }
  apply (Theorem12_6' u' v'); auto.
  - intro n. rewrite H11. apply H2.
  - intro n. rewrite H12. apply Rmult_le_pos; auto. left; assumption.
  - intro n. rewrite H11; rewrite H12. apply H6. apply le_plus_r.
  - generalize (Theorem12_3 v N H1). intros [I0 [a I1]]; auto.
    exists (k * a).
    assert (I2 : IsSeq {` λ n v0, v0 = v [(n + N)%nat] `}).
    { split.
      - unfold Function. intros x y z J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2; assumption.
      - apply AxiomI. intro n; split; intro J1; apply AxiomII; auto.
        exists (v[(n + N)%nat]). apply AxiomII'.
        reflexivity. }
    assert (I3 : ∀ n0, {` λ n v0, v0 = v [(n + N)%nat] `} [n0]
      = v[(n0 + N)%nat] ).
    { intro n0. apply f_x; try apply I2. apply AxiomII'.
      reflexivity. }
    assert (I4 : Series v' = {` λ n x,
      x = k * ((Series {` λ n v0, v0 = v [(n + N)%nat] `}) [n]) `}).
    { apply AxiomI.
      assert (J2 : ∀ n, Σ v' n = k * Σ
          {` λ(n : nat)(v0 : R),v0 = v [(n + N)%nat] `} n).
        { intro n. induction n as [|n IHn].
          - simpl. rewrite H12. rewrite I3. reflexivity.
          - simpl. rewrite Rmult_plus_distr_l. rewrite <- IHn.
            rewrite I3. rewrite H12. reflexivity. }
       intros [x y]; split; intro J1; apply AxiomII'.
      - applyAxiomII' J1. rewrite SeriesValue; auto.
        rewrite J1. apply J2.
      - applyAxiomII' J1. rewrite SeriesValue in J1; auto.
        rewrite J1. rewrite J2. reflexivity. }
    rewrite I4. apply Lemma12_1_1. apply I1.
Qed.

Theorem Theorem12_6 : ∀ (u v : Seq),
  IsSeq u -> IsSeq v -> PosSer u -> PosSer v ->
  (∃ N, ∀ n, (N < n)%nat -> u[n] <= v[n])
  -> (ConSer v -> ConSer u) /\ (DivSer u -> DivSer v).
Proof.
  intros u v H9 H10 H0 H1 [N H2].
  assert (H3 : Function {` λ m s, s = v[(m + S N)%nat] `}).
  { intros x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H4 : ∀ n, {` λ m s, s = v[(m + S N)%nat] `}[n]
    = v[(n + S N)%nat]).
  { intros x. apply f_x; try apply H3.
    apply AxiomII'. reflexivity. }
  assert (H5 : Function {` λ m s, s = u[(m + S N)%nat] `}).
  { intros x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H6 : ∀ n, {` λ m s, s = u[(m + S N)%nat] `}[n]
    = u[(n + S N)%nat]).
  { intros x. apply f_x; try apply H5.
    apply AxiomII'. reflexivity. }
  assert (H7 : ConSer {` λ m s, s = v[(m + S N)%nat] `} ->
    ConSer {` λ m s, s = u[(m + S N)%nat] `}).
  { apply Theorem12_6'.
    - intros n. rewrite H6. apply H0.
    - intros n. rewrite H4. apply H1.
    - intros n. rewrite H6. rewrite H4.
      apply H2. apply Nat.lt_lt_add_l.
      apply Nat.lt_succ_diag_r. }
  assert (H8 : ConSer v -> ConSer u).
  { intros I1. apply Theorem12_3 with (M := S N); auto.
    apply H7. apply Theorem12_3; auto. }
  split; auto. intros H11 H12. apply H11.
  auto.
Qed.

Theorem Theorem12_6_1 : ∀ (u v : Seq) (q : R),
  IsSeq u -> IsSeq v
  -> (∀ n, 0 < u[n]) -> (∀ n, 0 < v[n])
  -> limit_seq {` λ n s, s = (u[n]) / (v[n]) `} q
  -> 0 < q
  -> ConSer u <-> ConSer v.
Proof.
  intros u v q H0 H1 H2 H3 H4 H5.
  assert (H6 : 0 < q/2 < q). lra.
  destruct H6 as [H6 H7].
  destruct H4 as [H4 H8].
  apply H8 in H6 as H9.
  destruct H9 as [N H9].
  assert (H11 : PosSer u).
  { intros n. left. auto. }
  assert (H12 : PosSer v).
  { intros n. left. auto. }
  split; intros H10.
  - apply (Theorem12_6'' v u); auto.
    exists (S N). exists (2/q).
    assert (I1 : 0 < 2/q).
    { apply Rinv_0_lt_compat in H6.
      assert (I2 : 2 / q = / (q / 2)).
      { field. lra. }
      rewrite I2. assumption. }
    split; auto. intros n I2.
    apply -> Nat.le_succ_l in I2.
    apply H9 in I2. rewrite FunValueR in I2.
    apply Abs_R in I2.
    assert (I3 : q/2 < u[n]/v[n]). lra.
    assert (I4 : 0 < v [n] * (2 / q)).
    { apply Rmult_lt_0_compat; auto. }
    apply Rmult_lt_compat_r with (r := v[n]*(2/q)) in I3; auto.
    assert (I5 : q / 2 * (v [n] * (2 / q)) = v[n]).
    { field. lra. }
    rewrite I5 in I3.
    assert (I6 : u [n] / v [n] * (v [n] * (2 / q)) = 2 / q * u [n]).
    { field. generalize (H3 n). lra. }
    rewrite I6 in I3. left; auto.
  - apply (Theorem12_6'' u v); auto.
    exists (S N). exists (3*q/2).
    assert (I1 : 0 < 3*q/2). lra.
    split; auto. intros n I2.
    apply -> Nat.le_succ_l in I2.
    apply H9 in I2. rewrite FunValueR in I2.
    apply Abs_R in I2.
    assert (I3 : u[n]/v[n] < 3*q/2). lra.
    apply Rmult_lt_compat_r with (r := v[n]) in I3; auto.
    assert (I4 : u [n] / v [n] * v [n] = u[n]).
    { field. generalize (H3 n). lra. }
    rewrite I4 in I3. left; assumption.
Qed.

Theorem Theorem12_6_2 : ∀ (u v : Seq),
  IsSeq u -> IsSeq v
  -> (∀ n, 0 < u[n]) -> (∀ n, 0 < v[n])
  -> limit_seq {` λ n s, s = (u[n]) / (v[n]) `} 0
  -> ConSer v -> ConSer u.
Proof.
  intros u v H0 H1 H2 H3 H4 H5.
  assert (H6 : PosSer u).
  { intros n. left. auto. }
  assert (H7 : PosSer v).
  { intros n. left. auto. }
  apply (Theorem12_6'' u v); auto.
  assert (H8 : 0 < 1). lra.
  destruct H4 as [H4 H9].
  apply H9 in H8 as H10.
  destruct H10 as [N H10].
  exists (S N), 1. split; auto.
  intros n H11. apply -> Nat.le_succ_l in H11.
  apply H10 in H11. rewrite FunValueR in H11.
  apply Abs_R in H11. rewrite Rminus_0_r in H11.
  destruct H11 as [H11 H12].
  apply Rmult_lt_compat_r with (r := v[n]) in H12; auto.
  assert (H13 : u [n] / v [n] * v [n] = u[n]).
  { field. generalize (H3 n). lra. }
  rewrite H13 in H12. left; assumption.
Qed.

Theorem Theorem12_6_3 : ∀ (u v : Seq),
  IsSeq u -> IsSeq v
  -> (∀ n, 0 < u[n]) -> (∀ n, 0 < v[n])
  -> PosInfSeq {` λ n s, s = (u[n]) / (v[n]) `}
  -> ConSer u -> ConSer v.
Proof.
  intros u v H0 H1 H2 H3 [H4 H9] H5.
  assert (H6 : PosSer u).
  { intros n. left. auto. }
  assert (H7 : PosSer v).
  { intros n. left. auto. }
  assert (H8 : 0 < 1). lra.
  apply H9 in H8 as H10.
  destruct H10 as [N H10].
  apply (Theorem12_6 v u); auto.
  exists N. intros n H11.
  apply H10 in H11. rewrite FunValueR in H11.
  apply Rmult_lt_compat_r with (r := v[n]) in H11; auto.
  rewrite Rmult_1_l in H11.
  assert (H12 : u [n] / v [n] * v [n] = u[n]).
  { field. generalize (H3 n). lra. }
  rewrite H12 in H11.
  left. assumption.
Qed.

Lemma Lemma12_2_1 : ∀ x n, 0 < x -> 0 < x^^n.
Proof.
  intros x n H0. induction n as [|n IHn].
  - simpl. lra.
  - simpl. apply Rmult_lt_0_compat; assumption.
Qed.

Theorem Theorem12_7' : ∀ u q, IsSeq u -> (∀ n, 0 < u[n])
  -> 0 < q < 1 -> (∀ n, (u[S n])/(u[n]) <= q)
  -> ConSer u.
Proof.
  intros u q H0 H1 H2 H3.
  assert (H4 : ∀ n, u[n] <= u[O] * q^^n).
  { intros n. induction n as [|n IHn].
    - simpl. lra.
    - simpl. generalize (H3 n); intros I1.
      generalize (H1 n); intro I2.
      apply Rmult_le_compat_r with (r := u[n]) in I1; try lra.
      assert (I3 : u [S n] / u [n] * u [n] = u[S n]).
      { field. lra. }
      rewrite I3 in I1. clear I3.
      assert (I3 : q * u [n] <= u [0%nat] * (q * q ^^ n)).
      { rewrite (Rmult_comm q (q^^n)).
        rewrite <- Rmult_assoc. rewrite Rmult_comm.
        apply Rmult_le_compat_r; lra. }
      lra. }
  assert (H5 : Function {` λ m s, s = u[0%nat] * q^^m `}).
  { intros x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H6 : ∀ n, {` λ m s, s = u[0%nat] * q^^m `}[n]
    = u[0%nat] * q^^n).
  { intros x. apply f_x; try apply H5.
    apply AxiomII'. reflexivity. }
  apply Theorem12_6' with (v := {` λ m s, s = u[0%nat] * q^^m `}).
  - intros n. generalize (H1 n); intros I1. lra.
  - intros n. rewrite H6. apply Rmult_le_pos.
    + generalize (H1 O); intros I1. lra.
    + apply Rlt_le. apply Lemma12_2_1. apply H2.
  - intros n. rewrite H6. apply H4.
  - exists (u[0%nat] / (1 - q)).
    apply SeriesProportionalSequence. lra.
Qed.

Theorem Theorem12_7_1 : ∀ (u : Seq),
  IsSeq u -> (∀ n, 0 < u[n])
  -> (∃ N0 q, 0 < q < 1 /\ (∀ n, (N0 < n)%nat
    ->(u[S n])/(u[n]) <= q)) -> ConSer u.
Proof.
  intros u H0 H1 [N0 [q [H2 H3]]].
  assert (H4 : Function {` λ m s, s = u[(m + S N0)%nat] `}).
  { intros x y z J1 J2.
    applyAxiomII' J1; applyAxiomII' J2.
    rewrite J2; assumption. }
  assert (H6 : ∀ n, {` λ m s, s = u[(m + S N0)%nat] `}[n]
    = u[(n + S N0)%nat]).
  { intros x. apply f_x; try apply H4.
    apply AxiomII'. reflexivity. }
  assert (H7 : ConSer {` λ m s, s = u[(m + S N0)%nat] `}).
  { apply Theorem12_7' with (q := q); auto.
    - split; auto. apply AxiomI.
      intros z; split; intros I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (u[(z + S N0)%nat]).
        apply AxiomII'. reflexivity.
    - intros n. rewrite H6. apply H1.
    - intros n. rewrite H6. rewrite H6.
      apply H3. apply Nat.lt_lt_add_l.
      apply Nat.lt_succ_diag_r. }
  apply Theorem12_3 with (M := S N0); assumption.
Qed.

Theorem Theorem12_7_2 : ∀ (u : Seq),
  IsSeq u -> (∀ n, 0 < u[n])
  -> (∃ N0, ∀ n, (N0 < n)%nat -> 1 <= (u[S n])/(u[n]))
  -> DivSer u.
Proof.
  intros u H0 H1 [N0 H2] H3.
  generalize (Theorem12_1' u H0 H3).
  intros [H4 H5].
  generalize (H5 u[S N0] (H1 (S N0))).
  intros [N H6].
  assert (H7 : ∀ n, (N0 < n)%nat -> u[S N0] <= u[n]).
  { intros n I1. induction n as [|n IHn].
    - apply Nat.nlt_0_r in I1.
      contradiction.
    - apply lt_n_Sm_le in I1.
      apply le_lt_or_eq in I1 as [I1 | I1].
      + apply IHn in I1 as I2.
        generalize (H2 n I1).
        intros I3. assert (I4 : 0 <= u[n]).
        { apply Rlt_le. apply H1. }
        apply Rmult_le_compat_r with (r := u[n]) in I3; auto.
        rewrite Rmult_1_l in I3.
        assert (I5 : u [S n] / u [n] * u [n] = u[S n]).
        { field. apply Rgt_not_eq. apply H1. }
        rewrite I5 in I3. lra.
      + rewrite I1. lra. }
  assert (H8 : ∃ N1, (N0 < N1 /\ N < N1)%nat).
  { destruct (Nat.lt_ge_cases N0 N) as [I1 | I1].
    - exists (S N). split.
      + apply Nat.lt_lt_succ_r. assumption.
      + apply Nat.lt_succ_diag_r.
    - exists (S N0). split.
      + apply Nat.lt_succ_diag_r.
      + apply le_lt_n_Sm. assumption. }
  destruct H8 as [N1 [H8 H9]].
  generalize (H6 N1 H9); intro H10.
  generalize (H7 N1 H8); intros H11.
  rewrite Rminus_0_r in H10.
  apply Abs_R in H10. lra.
Qed.

(* 比式判别法的极限形式 *)
Theorem Theorem12_7_3 : ∀ (u : Seq), IsSeq u -> (∀ n, 0 < u[n])
  -> (∃ q, q < 1 /\ limit_seq {` λ n v, v = (u[S n]) / (u[n]) `} q)
  -> ConSer u.
Proof.
  intros u H0 H1 [q [H2 H3]].
  generalize H3; intros [H4 H5].
  assert (H6 : ∀ n, {` λ n v, v = (u[S n]) / (u[n]) `}[n]
    = (u[S n]) / (u[n])).
  { intros n. apply f_x; try apply H4.
    apply AxiomII'. reflexivity. }
  assert (H7 : 0 <= q).
  { apply (Theorem2_5_1 {` λ n v, v = (u[S n]) / (u[n]) `}); auto.
    exists O. intros n I1. rewrite H6.
    apply Rmult_le_pos.
    - apply Rlt_le. apply H1.
    - apply Rlt_le. apply Rinv_0_lt_compat.
      apply H1. }
  assert (H8 : 0 < 1 / 2 * (1 - q)). lra.
  apply H5 in H8 as H9.
  destruct H9 as [N H9].
  assert (H10 : ∀ n, (N < n)%nat -> u[S n]/u[n] <= 1/2 * (1 + q)).
  { intros n I1. apply H9 in I1.
    apply Abs_R in I1. rewrite H6 in I1.
    lra. }
  apply Theorem12_7_1; auto.
  exists N, (1/2 * (1 + q)). split; [lra | intros n I1].
  auto.
Qed.

Theorem Theorem12_7_4 : ∀ (u : Seq), IsSeq u -> (∀ n, 0 < u[n])
  -> (∃ q, 1 < q /\ limit_seq {` λ n v, v = (u[S n]) / (u[n]) `} q)
  -> DivSer u.
Proof.
  intros u H0 H1 [q [H2 H3]].
  generalize H3; intros [H4 H5].
  assert (H6 : ∀ n, {` λ n v, v = (u[S n]) / (u[n]) `}[n]
    = (u[S n]) / (u[n])).
  { intros n. apply f_x; try apply H4.
    apply AxiomII'. reflexivity. }
  assert (H7 : 0 <= q).
  { apply (Theorem2_5_1 {` λ n v, v = (u[S n]) / (u[n]) `}); auto.
    exists O. intros n I1. rewrite H6.
    apply Rmult_le_pos.
    - apply Rlt_le. apply H1.
    - apply Rlt_le. apply Rinv_0_lt_compat.
      apply H1. }
  assert (H8 : 0 < 1/2 * (q - 1)). lra.
  apply H5 in H8 as H9.
  destruct H9 as [N H9].
  assert (H10 : ∀ n, (N < n)%nat -> 1/2 * (1 + q) <= u[S n]/u[n]).
  { intros n I1. apply H9 in I1.
    apply Abs_R in I1. rewrite H6 in I1.
    lra. }
  apply Theorem12_7_2; auto.
  exists N. intros n I1.
  generalize (H10 n I1); intros I2.
  lra.
Qed.

Theorem Theorem12_7_5 : ∀ (u : Seq),
  IsSeq u -> (∀ n, 0 < u[n])
  -> PosInfSeq {` λ n v, v = (u[S n]) / (u[n]) `}
  -> DivSer u.
Proof.
  intros u H0 H1 [H2 H3].
  assert (H6 : ∀ n, {` λ n v, v = (u[S n]) / (u[n]) `}[n]
    = (u[S n]) / (u[n])).
  { intros n. apply f_x; try apply H2.
    apply AxiomII'. reflexivity. }
  generalize (H3 1 Rlt_0_1). intros [N H4].
  apply Theorem12_7_2; auto. exists N.
  intros n H5. apply Rlt_le.
  apply H4 in H5. rewrite H6 in H5.
  assumption.
Qed.

(* 定义：开方运算 *)
Definition Rooting (r : R) (n : nat)
  := cR \{ λ a, 0 <= a /\ a^^n = r \}.
Notation "n √ r" :=(Rooting r n) (at level 20).

Lemma Lemma12_2_2 : ∀ r n, (0 < n)%nat -> 0 <= r
  -> 0 <= (n √ r) /\ (n √ r)^^n = r.
Proof.
  intros r n H0 H1.
  assert (H2 : NotEmpty \{ λ a, 0 <= a /\ a^^n = r \}).
  { assert (I1 : NotEmpty \{ λ a, 0 <= a /\ a^^n <= r \}).
    { exists 0. apply AxiomII. split; try lra.
      destruct n as [|n].
      - apply Nat.nlt_0_r in H0.
        contradiction.
      - simpl. rewrite Rmult_0_l. assumption. }
    assert (I2 : (∃ M, Upper \{ λ a, 0 <= a /\ a^^n <= r \} M)).
    { destruct (Rle_or_lt r 1) as [J1 | J1].
      - exists 1. intros a J2.
        applyAxiomII J2. destruct J2 as [J2' J2].
        apply Rnot_gt_le.
        intros J3. assert (J4 : 1 < a^^n).
        { clear I1 J2.
          induction n as [|n IHn].
          - apply Nat.nlt_0_r in H0.
            contradiction.
          - destruct (Nat.eq_0_gt_0_cases n)
            as [K1 | K2].
            + rewrite K1. simpl. lra.
            + simpl. assert (K3 : 1 = 1 * 1). field.
              rewrite K3. generalize (IHn K2); intros K4.
               apply Rmult_gt_0_lt_compat; lra. }
        lra.
      - exists r. intros a J2.
        applyAxiomII J2. destruct J2 as [J2' J2].
        apply Rnot_gt_le.
        intros J3. assert (J4 : r < a^^n).
        { clear I1 J2.
          induction n as [|n IHn].
          - apply Nat.nlt_0_r in H0.
            contradiction.
          - destruct (Nat.eq_0_gt_0_cases n)
            as [K1 | K2].
            + rewrite K1. simpl. lra.
            + generalize (IHn K2); intros K4.
              simpl. assert (K5 : a^^n < a * a^^n).
              { pattern (a^^n) at 1.
                rewrite <- (Rmult_1_l (a^^n)).
                apply Rmult_lt_compat_r; lra. }
              lra. }
        lra. }
    generalize (Sup_principle \{ λ a, 0 <= a /\ a^^n <= r \}
      I1 I2); intros [a [I3 I4]].
    exists a. apply AxiomII.
    generalize (Lemma7 0 a n). intros I5.
    rewrite Rminus_0_r in I5.
    assert (I6 : ∀ x, {` λ x y, y = (x - 0) ^^ n `}[x]
      = x^^n).
    { intros x. apply f_x; try apply I5.
      apply AxiomII'. rewrite Rminus_0_r.
      reflexivity. }
    assert (I11 : 0 <= a).
    { apply I3. apply AxiomII.
      split; try lra.
      rewrite Lemma6_3_4; auto. }
      split; auto.
    apply NNPP. intros I7.
    destruct I5 as[I5 [δ' [I8 [I9 I10]]]].
    apply Rdichotomy in I7 as [I7 | I7].
    - assert (J1 : r - a^^n > 0). lra.
      apply I10 in J1 as J2.
      destruct J2 as [δ [J2 J3]].
      assert (J4 : 0 < Abs[a + δ/2 - a] < δ).
      { split; [apply Abs_not_eq_0 | apply Abs_R]; lra. }
      apply J3 in J4 as J5.
      rewrite I6 in J5. apply Abs_R in J5 as [J5 J6].
      apply Rplus_lt_reg_r in J6.
      assert (J7 : (a + δ/2) ∈ \{ λ a, 0 <= a /\ a^^n <= r \}).
      { apply AxiomII. lra. }
      apply I3 in J7. lra.
    - assert (J1 : a^^n - r > 0). lra.
      apply I10 in J1 as J2.
      destruct J2 as [δ [J2 J3]].
      assert (J4 : a - δ/2 < a). lra.
      apply I4 in J4 as J5.
      destruct J5 as [b [J5 J6]].
      applyAxiomII J5.
      assert (J7 : b ∈ \{ λ a, 0 <= a /\ a^^n <= r \}).
      { apply AxiomII. lra. }
      apply I3 in J7.
      destruct J7 as [J7 | J7].
      + assert (J8 : 0 < Abs[b - a] < δ).
        { split; [apply Abs_not_eq_0 | apply Abs_R]; lra. }
        apply J3 in J8.
        rewrite I6 in J8. apply Abs_R in J8.
        lra.
      + rewrite J7 in J5. lra. }
  apply AxiomcR in H2. applyAxiomII H2. apply H2.
Qed.

Lemma Lemma12_2_3 : ∀ a n, 0 <= a -> 0 <= a^^n.
Proof.
  intros a n [H0 | H0].
  - apply Rlt_le. apply Lemma12_2_1. assumption.
  - rewrite <- H0.
    destruct (Nat.eq_0_gt_0_cases n) as [I1 | I1].
    + rewrite I1. simpl. lra.
    + rewrite Lemma6_3_4; [lra | assumption].
Qed.

Lemma Lemma12_2_4 : ∀ a b n, 0 <= a -> 0 <= b -> (0 < n)%nat
  -> a < b -> a^^n < b^^n.
Proof.
  intros a b n H0 H1 H2 H3.
  induction n as [|n IHn].
  - apply Nat.nlt_0_r in H2.
    contradiction.
  - destruct (Nat.eq_0_gt_0_cases n) as [J1 | J2].
    + rewrite J1. simpl. lra.
    + apply IHn in J2. simpl.
      apply Rmult_le_0_lt_compat; try lra.
      apply Lemma12_2_3. assumption.
Qed.

Lemma Lemma12_2_5 : ∀ r n, (0 < n)%nat -> 0 < r -> 0 < (n √ r).
Proof.
  intros r n H0 H1.
  apply Rlt_le in H1 as H2.
  generalize (Lemma12_2_2 r n H0 H2).
  intros H3.
  destruct H3 as [[H3 | H3] H4]; auto.
  rewrite <- H3 in H4.
  rewrite Lemma6_3_4 in H4; auto.
  lra.
Qed.

Lemma Lemma12_2_6 : ∀ a r n, (0 < n)%nat -> 0 <= a
  -> a^^n = r -> n √ r = a.
Proof.
  intros a r n H0 H1 H2.
  generalize (Lemma12_2_3 a n H1).
  rewrite H2. intros H4.
  generalize (Lemma12_2_2 r n H0 H4).
  intros H5.
  destruct H5 as [H5 H6].
  apply NNPP. intros H8.
  apply Rdichotomy in H8 as [H8 | H8];
  apply Lemma12_2_4 with (n := n) in H8; auto; lra.
Qed.

Lemma Lemma12_2_8 : ∀ n, 1 ^^ n = 1.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn. field.
Qed.

Lemma Lemma12_2_7 : ∀ a b n, 0 <= a -> 0 <= b
  -> a <= b -> a^^n <= b^^n.
Proof.
  intros a b n H0 H1 H2.
  induction n as [|n IHn].
  - simpl. lra.
  - simpl. apply Rmult_le_compat; auto.
    apply Lemma12_2_3. assumption.
Qed.

(* 根式判别法 *)
Theorem Theorem12_8_1 : ∀ u : Seq, IsSeq u -> PosSer u
  -> (∃ N q, ∀ n, (N < n)%nat -> n √ u[n] <= q < 1)
  -> ConSer u.
Proof.
  intros u H0 H1 [N [q H2]].
  assert (H3 : IsSeq {` λ m s, s = 1 * q^^m `}).
  { apply IsProportionalSequence. }
  assert (H4 : ∀ n, {` λ m s, s = 1 * q^^m `}[n] = q^^n).
  { intros n. apply f_x; try apply H3.
    apply AxiomII'. field. }
  assert (H5 : 0 <= q < 1).
  { generalize (H2 (S N) (Nat.lt_succ_diag_r N)).
    intros I1.
    generalize(Lemma12_2_2 (u[S N]) (S N)
      (Nat.lt_0_succ N) (H1 (S N))).
    intros [I2 I3]. lra. }
  destruct H5 as [H5 H6].
  apply Theorem12_6 with (v := {` λ m s, s = 1 * q^^m `}); auto.
  - intros n . rewrite H4. apply Lemma12_2_3.
    assumption.
  - exists N. intros n I1. apply H2 in I1 as I2.
    destruct I2 as [I2 I3]. rewrite H4.
    assert (I4 : (0 < n)%nat).
    { eapply Nat.lt_lt_0; eauto. }
    generalize (Lemma12_2_2 (u[n]) n I4 (H1 n)).
    intros [I5 I6].
    apply Lemma12_2_7 with (n := n) in I2; auto.
    rewrite I6 in I2. assumption.
  - exists (1 / (1 - q)).
    apply SeriesProportionalSequence.
    lra.
Qed.

Theorem Theorem12_8_2 : ∀ u : Seq, IsSeq u -> PosSer u
  -> (∃ N, ∀ n, (N < n)%nat -> 1 <= n √ u[n])
  -> DivSer u.
Proof.
  intros u H0 H1 [N H2] H3.
  apply Theorem12_1' in H3 as H4; auto.
  destruct H4 as [H4 H5].
  assert (H6 : 1/2 > 0). lra.
  apply H5 in H6 as [N1 H6].
  generalize (Max_nat_2 N N1).
  intros [n [H7 H8]].
  apply H2 in H7. apply H6 in H8 as H9.
  assert (H10 : (0 < n)%nat).
  { eapply Nat.lt_lt_0; eauto. }
  assert (H11 : 0 <= n √ u [n]).
  { apply Lemma12_2_2; auto. }
  assert (H12 : 0 <= 1). lra.
  apply Lemma12_2_7 with (n := n) in H7; auto.
  rewrite Lemma12_2_8 in H7.
  unfold PosSer in H1.
  generalize (Lemma12_2_2 (u[n]) n H10 (H1 n)).
  intros [H13 H14]. rewrite H14 in H7.
  rewrite Rminus_0_r in H9.
  rewrite Abs_ge in H9; [lra | apply Rle_ge].
  auto.
Qed.

Theorem Theorem12_8_3 : ∀ u q, IsSeq u -> PosSer u
  -> q < 1 -> limit_seq {` λ n v, v = n √ u[n] `} q
  -> ConSer u.
Proof.
  intros u q H0 H1 H2 [H3 H4].
  assert (H5 : (1 - q)/2 > 0). lra.
  apply H4 in H5 as [N H5].
  apply Theorem12_8_1; auto.
  exists N, ((1 + q)/2). intros n H6.
  apply H5 in H6.
  assert (H7 : {` λ n v, v = n √ u[n] `}[n] = n √ u[n]).
  { apply f_x; [apply H3 | apply AxiomII'].
    reflexivity. }
  rewrite H7 in H6.
  apply Abs_R in H6. lra.
Qed.

Theorem Theorem12_8_4 : ∀ u q, IsSeq u -> PosSer u
  -> 1 < q -> limit_seq {` λ n v, v = n √ u[n] `} q
  -> DivSer u.
Proof.
  intros u q H0 H1 H2 [H3 H4].
  assert (H5 : (q - 1)/2 > 0). lra.
  apply H4 in H5 as [N H5].
  apply Theorem12_8_2; auto.
  exists N. intros n H6.
  apply H5 in H6.
  assert (H7 : {` λ n v, v = n √ u[n] `}[n] = n √ u[n]).
  { apply f_x; [apply H3 | apply AxiomII'].
    reflexivity. }
  rewrite H7 in H6.
  apply Abs_R in H6. lra.
Qed.

Theorem Theorem12_8_5 : ∀ u, IsSeq u -> PosSer u
  -> PosInfSeq {` λ n v, v = n √ u[n] `}
  -> DivSer u.
Proof.
  intros u H0 H1 H2.
  assert (H5 : 1 > 0). lra.
  apply H2 in H5 as [N H5].
  apply Theorem12_8_2; auto.
  exists N. intros n H6.
  apply H5 in H6.
  rewrite FunValueR in H6. lra.
Qed.

End A12_2.

Export A12_2.
