Require Export A_12_2.

Module A12_3.

Lemma Lemma12_3_1 : ∀ u q, IsSeq u ->
  limit_seq {` λ n v, v = u[(2*n)%nat] `} q ->
  limit_seq {` λ n v, v = u[S (2*n)%nat] `} q ->
  limit_seq u q.
Proof.
  intros u q H0 [H1 H2] [H3 H4].
  split; auto. intros ε H5.
  generalize (H2 ε H5). intros [N1 H6].
  generalize (H4 ε H5). intros [N2 H7].
  assert (H8 : ∀ n, {` λ n v, v = u[(2*n)%nat] `}[n] = u[(2*n)%nat]).
  { intros n. apply f_x; [apply H1 | apply AxiomII'].
    reflexivity. }
  assert (H9 : ∀ n, {` λ n v, v = u[S (2*n)%nat] `}[n] = u[S (2*n)%nat]).
  { intros n. apply f_x; [apply H3 | apply AxiomII'].
    reflexivity. }
  generalize (Max_nat_2 (2*N1)%nat (S (2*N2)%nat)).
  intros [N [H10 H11]]. exists N. intros n H12.
  generalize (ArithProp.even_odd_cor n).
  intros [p [H13 | H13]].
  - assert (I1 : (p > N1)%nat).
    { apply Nat.mul_lt_mono_pos_l with (p := 2%nat); auto.
      rewrite <- H13. eapply Nat.lt_trans; eauto. }
    apply H6 in I1. rewrite H8 in I1.
    rewrite H13. assumption.
  - assert (I1 : (p > N2)%nat).
    { apply Nat.mul_lt_mono_pos_l with (p := 2%nat); auto.
      apply lt_S_n. rewrite <- H13.
      eapply Nat.lt_trans; eauto. }
    apply H7 in I1. rewrite H9 in I1.
    rewrite H13. assumption.
Qed.

Lemma Lemma12_3_2 : ∀ (X Y : Type) (f g : X -> Y),
  (∀ x, f x = g x) -> {` λ x y, y = f x `} = {` λ x y, y = g x `}.
Proof.
  intros X Y f g H0. apply AxiomI.
  intros [x y]; split; intros H1;
  applyAxiomII' H1; apply AxiomII'.
  - rewrite H1. apply H0.
  - rewrite H0. assumption.
Qed.

(* 莱布尼兹判别法 *)
Theorem Theorem12_11 : ∀ u, (∀ n, u[S n] <= u[n])
  -> PosSer u -> limit_seq u 0
  -> ConSer {` λ n v, v = (-1)^^n * u[n] `}.
Proof.
  intros u H0 H5 H1.
  assert (H2 : ∃ u', u' = Series {` λ n v, v = (-1)^^n * u[n] `}).
  { exists (Series {` λ n v, v = (-1)^^n * u[n] `}).
    reflexivity. }
  destruct H2 as [u' H2]. unfold ConSer. rewrite <- H2.
  assert (H8 : ∀ k, (-1) ^^ S (S (2 * k)) = 1).
  { intros k. induction k as [|k IHk].
    - simpl. field.
    - simpl in *. rewrite Nat.add_succ_r.
      simpl. rewrite IHk. field. }
  assert (H3 : IncreaseSeq {` λ n v, v = u'[S (2*n)%nat] `}).
  { split.
    - apply FunIsSeq.
    - intros n. repeat rewrite H2.
      unfold Series.
      repeat rewrite FunValueR.
      assert (I1 : (2 * S n = S (S (2 * n)))%nat).
      { simpl. rewrite Nat.add_succ_r.
        reflexivity. }
      rewrite I1. simpl Σ.
      repeat rewrite FunValueR.
      assert (I2 : (2 * n = n + (n + 0))%nat).
      { simpl. reflexivity. }
      rewrite <- I2 in *.
      assert (I3 : 0 <= (-1) ^^ S (S (2 * n)) * u [S (S (2 * n))]
        + (-1) ^^ S (S (S (2 * n))) * u [S (S (S (2 * n)))]).
      { rewrite H8.
        assert (J2 : ∀ k, (-1) ^^ S (S (S (2 * k))) = -1).
        { intros k. induction k as [|k IHk].
          - simpl. field.
          - simpl in *. rewrite Nat.add_succ_r.
            simpl. rewrite IHk. field. }
        rewrite J2. generalize (H0 (S (S (2 * n)))). lra. }
      lra. }
  assert (H7 : ∀ k, (-1) ^^ (S (2 * k)) = -1).
  { intros k. induction k as [|k IHk].
    - simpl. field.
    - simpl in *. rewrite Nat.add_succ_r.
      simpl. rewrite IHk. field. }
  assert (H4 : ∀ n, u'[(2 * n)%nat] <= u[O]).
  { intros n. rewrite H2. unfold Series.
    induction n as [|n IHn].
    - rewrite FunValueR. simpl.
      repeat rewrite FunValueR. simpl. lra.
    - rewrite FunValueR. simpl.
      rewrite Nat.add_succ_r in *.
      simpl. assert (I1 : (2*n = n + (n + 0))%nat).
      { simpl. reflexivity. }
      rewrite <- I1 in *.
      repeat rewrite FunValueR.
      assert (I2 : (-1) ^^ S (2 * n) * u [S (2 * n)] +
        (-1) ^^ S (S (2 * n)) * u [S (S (2 * n))] <= 0).
      { rewrite H8. rewrite H7.
        generalize (H0 (S (2 * n))). lra. } 
      rewrite FunValueR in IHn. lra. }
  assert (H6 : ∀ n, u'[S (2 * n)] <= u[O]).
  { intros n. rewrite H2 in *.
    unfold Series in *. rewrite FunValueR in *.
    simpl. rewrite FunValueR. generalize (H4 n); intros I1.
    rewrite FunValueR in I1.
    assert (I2 : (-1) ^^ S (n + (n + 0)) * u [S (n + (n + 0))] <= 0).
    { simpl in H7. simpl. rewrite H7.
      generalize (H5 (S (n + (n + 0)))).
      lra. }
    simpl in I1. lra. }
  assert (H30 : ∀ k, (k + (k + 0) = 2 * k)%nat).
  {intros k. simpl. reflexivity. }
  assert (H9 : BoundedSeq {` λ n v, v = u'[S (2*n)%nat] `}).
  { split; try apply FunIsSeq.
    assert (I1 : ∀ k, u[O] - u[1%nat] <= u'[S (2*k)]).
    { intros k. rewrite H2. induction k as [|k IHk].
      - rewrite SeriesValue. simpl.
        repeat rewrite FunValueR.
        simpl. lra.
      - rewrite SeriesValue. simpl.
        repeat rewrite FunValueR.
        rewrite Nat.add_succ_r in *.
        rewrite H30 in *. rewrite H8.
        assert (I2 : (S (S (2 * k)) = 2 * (S k))%nat).
        { simpl. rewrite Nat.add_succ_r.
          reflexivity. }
        rewrite I2. rewrite H7.
        generalize (H5 (2 * S k)%nat).
        generalize (H5 (S (2 * S k))%nat).
        generalize (H0 (2 * S k)%nat).
        rewrite SeriesValue in IHk.
        lra. }
    assert (I2 : ∃ M, Abs[u[0%nat] - u[1%nat]] <= M
      /\ Abs[u[0%nat]] <= M).
    { destruct (Rlt_or_le Abs[u[0%nat] - u[1%nat]]
        Abs[u[0%nat]]) as [J1 | J1];
        [exists Abs[u[0%nat]] |
          exists Abs[u[0%nat] - u[1%nat]]]; lra. }
      destruct I2 as [M [I2 I3]].
      exists M. intros n.
      rewrite FunValueR. apply Abs_le_R.
      apply Abs_le_R in I2.
      apply Abs_le_R in I3.
      generalize (H6 n).
      generalize (I1 n). lra. }
  apply Theorem2_9 in H9 as H10;
  [idtac | left; auto].
  destruct H10 as [A H10].
  assert (H11 : IsSeq u').
  { rewrite H2. apply SeriesSeq. }
  exists A. apply Lemma12_3_1; auto.
  split; try apply FunIsSeq.
  destruct H10 as [H10 H12].
  intros ε H13. assert (H14 : ε/2 > 0). lra.
  apply H12 in H14 as H15.
  destruct H15 as [N1 H15].
  generalize H1. intros [H16 H17].
  generalize (H17 (ε/2) H14). intros [N2 H18].
  generalize (Max_nat_2 N1 N2).
  intros [N [H19 H20]].
  exists N. intros n H21.
  rewrite FunValueR.
  destruct n as [|n].
  - apply Nat.nlt_0_r in H21.
    contradiction.
  - apply lt_n_Sm_le in H21 as H22.
    assert (H23 : (n > N1)%nat).
    { eapply Nat.lt_le_trans; eauto. }
    apply H15 in H23. rewrite FunValueR in H23.
    assert (H24 : (N2 < 2 * S n)%nat).
    { simpl. rewrite Nat.add_succ_r.
      repeat apply Nat.lt_lt_succ_r.
      apply Nat.lt_lt_add_r.
      eapply Nat.lt_le_trans; eauto. }
    apply H18 in H24.
    assert (H25 : u' [(2 * S n)%nat] - A =
      u' [S (2 * n)] - A + (u [(2 * S n)%nat] - 0)).
    { rewrite H2. repeat rewrite SeriesValue.
      simpl. repeat rewrite Nat.add_succ_r.
      simpl. repeat rewrite FunValueR.
      pattern (n + (n + 0))%nat at 4.
      rewrite H30. rewrite H8. field. }
    rewrite H25.
    generalize (Abs_plus_le (u' [S (2 * n)] - A)
      (u [(2 * S n)%nat] - 0)). lra.
Qed.

(* 定义: 绝对收敛 *)
Definition AbsoluteCon (u : Seq) :=
  ConSer {` λ n v, v = Abs[u[n]] `}.

(* 定理: 若一个级数绝对收敛，则该级数一定收敛 *)
Theorem Theorem12_12 : ∀ u, AbsoluteCon u -> ConSer u.
Proof.
  intros u [a H0].
  assert (H1 : ∃ v, v = {` λ n w, w = (u[n] + Abs[u[n]]) / 2 `}).
  { exists {` λ n w, w = (u[n] + Abs[u[n]]) / 2 `}.
    reflexivity. }
  destruct H1 as [v H1].
  assert (H2 : IsSeq v).
  { rewrite H1. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists ((u[n] + Abs[u[n]]) / 2).
      apply AxiomII'. reflexivity. }
  assert (H3 : ∀ n, v[n] = (u[n] + Abs[u[n]]) / 2).
  { intro n. apply f_x; try apply H2. rewrite H1.
    apply AxiomII'. reflexivity. }
  assert (H4 : IsSeq {` λ n v, v = Abs[u[n]] `}).
  { split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists (Abs[u[n]]).
      apply AxiomII'. reflexivity. }
  assert (H5 : ∀ n, {` λ n v, v = Abs[u[n]] `} [n]
    = Abs[u[n]]).
  { intro n. apply f_x; try apply H4.
    apply AxiomII'. reflexivity. }
  assert (H6 : Convergence (Series v)).
  { apply Theorem12_6' with (v := {` λ n v, v = Abs[u[n]] `}); auto.
    - intro n. rewrite H3. destruct (Rle_or_lt 0 u[n]) as [I1 | I1].
      + apply Rle_ge in I1. rewrite Abs_ge; auto. lra.
      + rewrite Abs_lt; auto. lra.
    - intro n. rewrite H5. apply Rge_le. apply Abs_Rge0.
    - intro n. rewrite H3; rewrite H5.
      destruct (Rle_or_lt 0 u[n]) as [I1 | I1].
      + apply Rle_ge in I1. rewrite Abs_ge; auto. lra.
      + pattern (Abs[u[n]]) at 1. rewrite Abs_lt; auto.
        generalize (Abs_Rge0 u[n]). intro I2. lra.
    - exists a. assumption. }
  assert (H7 : ∀ n, u[n] = 2 * v[n] - Abs[u[n]]).
  { intro n. rewrite H3.
    destruct (Rle_or_lt 0 u[n]) as [I1 | I1].
    - apply Rle_ge in I1. rewrite Abs_ge; auto. lra.
    - rewrite Abs_lt; auto. lra. }
  destruct H6 as [b H6]. exists (2 * b - a).
  generalize (SeriesSeq u); intros H11. split; auto.
  intros ε H12. assert (H13 : (2 / 3) * ε > 0). lra.
  assert (H14 : (1 / 3) * ε > 0). lra.
  apply H6 in H14 as H15. destruct H15 as [N2 H15].
  apply H0 in H14 as H16. destruct H16 as [N1 H16].
  generalize (Max_nat_2 N1 N2). intros [N [H17 H18]].
  exists N. intros n H19. rewrite SeriesValue; auto.
  assert (H20 : ∀ k, Σ u k = 2 * Σ v k
    - Σ {` λ n v, v = Abs[u[n]] `} k).
  { intro k. induction k as [|k IHk].
    - simpl. rewrite H5. apply H7.
    - simpl. rewrite H5.
      assert (I1 : 2 * (Σ v k + v [S k]) -
        (Σ {` λ n v, v = Abs[u[n]] `} k +
         Abs [u [S k]]) = 2 * Σ v k -
         Σ {` λ n v, v = Abs[u[n]] `} k +
         2 * v[S k] - Abs [u [S k]] ).
      field. rewrite I1. clear I1. rewrite <- IHk.
      pattern (u[S k]) at 1.
      rewrite H7. unfold Rminus. rewrite <- Rplus_assoc.
      reflexivity. }
  rewrite H20.
  assert (H21 : 2 * Σ v n -
    Σ {` λ n v, v = Abs[u[n]] `} n -
    (2 * b - a) = 2 * (Σ v n - b) -
    (Σ {` λ n v, v = Abs[u[n]] `} n - a)).
  field. rewrite H21. clear H21.
  generalize (Abs_minus_le (2 * (Σ v n - b))
    (Σ {` λ n v, v = Abs[u[n]] `} n - a)).
  intro H21.
  apply Rle_lt_trans with (r2 := Abs[2 * (Σ v n - b)] +
      Abs[Σ {` λ n v, v = Abs[u[n]] `} n - a]); auto.
  clear H21. assert (H21 : ε = 2 * ((1 / 3) * ε) + (1 / 3) * ε).
  field. rewrite H21. clear H21.
  apply Rplus_lt_compat.
  - rewrite Abs_mult. rewrite Abs_ge; try lra.
    assert (H21 : (n > N2)%nat).
    { apply Nat.lt_trans with (m := N); auto. }
    generalize (H15 n H21); intro H22.
    rewrite SeriesValue in H22; auto. lra.
  - assert (I1 : (n > N1)%nat).
    { apply Nat.lt_trans with (m := N); auto. }
    generalize (H16 n I1); intro I2.
    rewrite SeriesValue in I2; auto.
Qed.

End A12_3.

Export A12_3.