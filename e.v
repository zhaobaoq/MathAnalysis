Require Export A_14_2.

Module A_e.

Lemma pow_lt_0 : ∀ (a : R) (n : nat), 0 < a -> 0 < a^^n.
Proof.
  intros a n H0. induction n as [| n IHn].
  - simpl. lra.
  - simpl. apply Rmult_lt_0_compat; auto.
Qed.

Lemma pow_lt : ∀ (a b : R) (n : nat), (0 < n)%nat -> 0 < a < b
  -> a^^n < b^^n.
Proof.
  intros a b n H0 H1. induction n as [| n IHn].
  - exfalso. apply Nat.lt_irrefl in H0. assumption.
  - apply lt_n_Sm_le in H0. apply le_lt_or_eq in H0.
    apply or_comm in H0. destruct H0 as [H0 | H0].
    + rewrite <- H0. simpl. lra.
    + apply IHn in H0 as H2. simpl. destruct H1 as [H1 H3].
      generalize (pow_lt_0 a n H1). intro H4.
      apply Rmult_gt_0_lt_compat; lra.
Qed.

Lemma Inequality' : ∀ (a b : R) (n : nat), 0 < a < b -> (0 < n)%nat
  -> b^^(S n) - a^^(S n) < (INR (S n)) * b^^n * (b - a).
Proof.
  intros a b n H0. induction n as [| n IHn].
  - intro H1. apply Nat.lt_irrefl in H1. exfalso. assumption.
  - intro H1. apply lt_n_Sm_le in H1. apply le_lt_or_eq in H1.
    apply or_comm in H1.
    destruct H1 as [H1 | H1].
    + rewrite <- H1 in *. simpl. rewrite Rmult_1_r in *.
      rewrite Rmult_1_r.
      assert (H2 : b * b - a * a = (b + a) * (b - a)). field.
      rewrite H2. apply Rmult_lt_compat_r; lra.
    + apply IHn in H1 as H2.
      assert (H3 : b^^(S (S n)) - a^^(S (S n))
        = b * (b^^(S n) - a^^(S n)) + a^^(S n) * (b - a)).
      simpl. field. rewrite H3.
      assert (H4 : b * (b^^(S n) - a^^(S n)) + a^^(S n) * (b - a)
        < b * (INR (S n) * b^^n * (b - a)) + a^^(S n) * (b - a)).
      { apply Rplus_lt_compat_r. apply Rmult_lt_compat_l; lra. }
      apply Rlt_trans with (r2 := b * (INR (S n) * pow b n * (b - a))
        + pow a (S n) * (b - a)); auto.
      rewrite <- Rmult_assoc. rewrite <- Rmult_assoc.
      rewrite <- Rmult_plus_distr_r.
      apply Rmult_lt_compat_r; try lra.
      assert (H5 : INR (S (S n)) * b^^(S n)
        = b * INR (S n) * b^^n + b^^(S n)).
      simpl. field.
      rewrite H5. apply Rplus_lt_compat_l. apply pow_lt; auto.
Qed.

Lemma Inequality : ∀ (a b : R) (n : nat), 0 < a < b -> (0 < n)%nat
  -> a^^(S n) > b^^n * ((INR (S n)) * a - (INR n) * b).
Proof.
  intros a b n H0 H1. generalize (Inequality' a b n H0 H1). intro H2.
  assert (H3 : pow a (S n) > pow b (S n) - INR (S n) * pow b n * (b - a)).
  lra. assert (H4 : pow b (S n) - INR (S n) * pow b n * (b - a)
    = pow b n * (INR (S n) * a - INR n * b)).
  { simpl pow. rewrite S_INR. field. }
  rewrite <- H4. assumption.
Qed.

Lemma odd_even : ∀ n : nat, ∃ m, (n = m + m \/ n = m + m + 1)%nat.
Proof.
  intro n. induction n as [|n IHn].
  - exists 0%nat. left. simpl. reflexivity.
  - destruct IHn as [m [IHn | IHn]].
    + exists m. right. rewrite IHn. rewrite Nat.add_1_r.
      reflexivity.
    + exists (S m). left. rewrite IHn. rewrite Nat.add_1_r.
      simpl. rewrite (Nat.add_comm m (S m)).
      simpl. reflexivity.
Qed.

Theorem limit_e : ∃ (e : R), limit_seq
  {` λ n v, v = (1 + 1 / (INR (S n)))^^(S n) `} e.
Proof.
  assert (H0 : IsSeq {` λ n v, v = pow (1 + 1 / (INR (S n))) (S n) `}).
  { split.
    - unfold Function. intros x y z I1 I2. apply -> AxiomII' in I1.
      lazy beta in I1. apply -> AxiomII' in I2. lazy beta in I2.
      rewrite I2. assumption.
    - apply AxiomI. intro n; split; intro I1.
      + apply AxiomII. reflexivity.
      + apply AxiomII. exists (pow (1 + 1 / (INR (S n))) (S n)).
        apply AxiomII'. reflexivity. }
  assert (H1 : ∀ (n : nat), {` λ n v, v
    = pow (1 + 1 / (INR (S n))) (S n) `} [n]
    = pow (1 + 1 / (INR (S n))) (S n)).
  { destruct H0 as [H0 I1]. intro n. apply f_x; auto.
    apply AxiomII'. reflexivity. }
  generalize Nat.lt_0_succ. intro H2.
  assert (H3 : IncreaseSeq {` λ n v, v
    = (1 + 1 / (INR (S n)))^^(S n) `}).
  { unfold IncreaseSeq. split; auto.
    intro n. rewrite H1. rewrite H1.
    assert (H3 : 0 < (1 + 1 / (INR (S (S n)))) < (1 + 1 / (INR (S n)))).
    { generalize (pos_INR n). intro I1. rewrite S_INR. rewrite S_INR.
      assert (I2 : 0 < (INR n + 1) < (INR n + 1 + 1)). lra.
      assert (I3 : 0 < (INR n + 1) * (INR n + 1 + 1)).
      { apply Rmult_gt_0_compat; lra. }
      assert (I4 : / (INR n + 1 + 1) < / (INR n + 1)).
      { apply Rinv_lt_contravar; lra. }
      assert (I5 : 0 < / (INR n + 1 + 1)).
      { apply Rinv_0_lt_compat; lra. }
      lra. }
    generalize (Inequality (1 + 1 / INR (S (S n)))
      (1 + 1 / INR (S n)) (S n) H3 (H2 n)). intro H4.
    assert (H5 : INR (S (S n)) * (1 + 1 / INR (S (S n))) -
      INR (S n) * (1 + 1 / INR (S n)) = 1).
    { rewrite S_INR. rewrite S_INR. field.
      generalize (pos_INR n). intro I1. split; lra. }
    rewrite H5 in H4. lra. }
  apply Theorem2_9. left. auto.
  unfold BoundedSeq. split; auto. exists 4.
  assert (H4 : ∀ n, pow (1 + 1 / (2 * INR (S n))) (S n + S n) < 2 * 2).
  { intro n. assert (H5 : 0 < 1 < 1 + 1 / (2 * INR (S n))).
    { split; try lra. rewrite S_INR. generalize (pos_INR n).
      intro H5. assert (H6 : 2 * (INR n + 1) > 0). lra.
      assert (H7 : 1 / (2 * (INR n + 1)) > 0).
      { apply Rdiv_lt_0_compat; lra. }
      lra. }
    generalize (Inequality 1 (1 + 1 / (2 * INR (S n))) (S n) H5 (H2 n)).
    intro H6. assert (H7 : ∀ n, pow 1 n = 1).
    { intro n0. induction n0 as [|n0 IHn].
      - simpl. reflexivity.
      - simpl. rewrite IHn. field. }
    rewrite H7 in H6.
    assert (H8 : INR (S (S n)) * 1 - INR (S n)
      * (1 + 1 / (2 * INR (S n))) = 1 / 2).
    { rewrite S_INR. field. rewrite S_INR.
      generalize (pos_INR n). lra. }
    rewrite H8 in H6.
    assert (H9 : (1 + 1 / (2 * INR (S n)))^^(S n) < 2). lra.
    assert (H10 : ∀ a (m k : nat), (pow a m) * (pow a k) = pow a (m + k)).
    { intros a m k. induction m as [|m IHm].
      - simpl. field.
      - simpl. rewrite Rmult_assoc. rewrite IHm. reflexivity. }
    assert (H11 : ∀ a m, a > 0 -> 0 < pow a m).
    { intros a m I1. induction m as [|m IHm].
      - simpl. lra.
      - simpl. apply Rmult_lt_0_compat; auto. }
    assert (H12 : 0 < 1 + 1 / (2 * INR (S n))).
    { rewrite S_INR. generalize (pos_INR n). intro I1.
      assert (I2 : 2 * (INR n + 1) > 0). lra.
      assert (I3 : 1 / (2 * (INR n + 1)) > 0).
      { apply Rdiv_lt_0_compat; lra. }
      lra. }
    assert (H13 : (pow (1 + 1 / (2 * INR (S n))) (S n))
      * (pow (1 + 1 / (2 * INR (S n))) (S n)) < 2 * 2).
    { apply Rmult_le_0_lt_compat; auto; left; apply H11; auto. }
    rewrite H10 in H13. auto. }
  intro n. rewrite H1.
  assert (H5 : ∀ n, pow (1 + 1 / INR (S n)) (S n) > 0).
  { intro n0. unfold IncreaseSeq in H3. induction n0 as [|n0 IHn].
    - simpl. lra.
    - destruct H3 as [H3 I1]. generalize (I1 n0). intro I2.
      rewrite H1 in I2. rewrite H1 in I2. lra. }
  rewrite Abs_gt; auto.
  assert (H6 : ∀ n, 2 * INR (S n) = INR (S n) + INR (S n)).
  { intro n0. field. }
  apply -> EqualIncrease in H3. destruct H3 as [H3 H7].
  assert (H8 : (n < n + S n)%nat).
  { apply Nat.lt_lt_add_l. apply Nat.lt_succ_diag_r. }
  apply H7 in H8 as H9. rewrite H1 in H9. rewrite H1 in H9.
  assert (H10 : (S (n + S n) = S n + S n)%nat).
  { simpl. reflexivity. }
  rewrite H10 in H9.
  assert (H11 : (INR (S n + S n) = 2 * (INR (S n))%nat)).
  { rewrite plus_INR. ring. }
  rewrite H11 in H9.
  generalize (H4 n). intro H12. lra.
Qed.

End A_e.

Export A_e.