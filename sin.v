Require Export A_12_3.

Lemma factorial_lt_0_r : ∀ n, 1 <= INR (n!).
Proof.
  intro n. assert (H0 : 1 = INR (1%nat)).
  { simpl. reflexivity. }
  rewrite H0.
  apply le_INR. induction n as [|n IHn].
  - simpl. apply le_n.
  - simpl. apply le_plus_trans; assumption.
Qed.

(* 定理: 用来定义正弦函数的级数是收敛的 *)
Theorem SinSeries : ∀ x, ConSer {` λ k v, v =
  (-1)^^k * x^^(S (2*k)%nat) / INR ((S (2*k)%nat)!) `}.
Proof.
  intro x.
  assert (H0 : ∃ u, u = {` λ k v, v =
    (pow (-1) k) * (pow x (S (2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `} ).
  { exists {` λ k v, v =
    (pow (-1) k) * (pow x (S (2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `}; reflexivity. }
  destruct H0 as [u H0].
  assert (H1 : IsSeq u ).
  { rewrite H0. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists ((pow (-1) k) * (pow x (S (2 * k)%nat))
        / INR ((S (2 * k)%nat)!)).
      apply AxiomII'. reflexivity. }
  assert (H2 : ∀ k, u[k] = (pow (-1) k)
    * (pow x (S (2 * k)%nat)) / INR ((S (2 * k)%nat)!)).
  { intro k. apply f_x; try apply H1. rewrite H0.
    apply AxiomII'. reflexivity. }
  assert (H9 : ∀ k, 0 < INR (S (2 * k) !)).
  { intro k. apply lt_0_INR. apply Lemma6_3_1. }
  destruct classic with (P := x = 0) as [H6 | H6].
  - rewrite H6 in *. assert (H3 : ∀ k, pow 0 (S k) = 0).
    { intro k. induction k as [|k IHk]; simpl; field. }
    exists 0. rewrite <- H0.
    generalize (SeriesSeq u); intros H4.
    split; auto. intros ε H5. exists 0%nat. intros n H7.
    rewrite SeriesValue; auto.
    assert (H8 : ∀ k, Σ u k = 0).
    { intro k. induction k as [|k IHk].
      - simpl. rewrite H2. rewrite H3. field.
        apply Rgt_not_eq. apply H9.
      - simpl. rewrite H2. rewrite H3. rewrite IHk.
        field. apply Rgt_not_eq. apply H9. }
    rewrite H8. rewrite Abs_ge; lra.
  - rewrite <- H0. apply Theorem12_12.
    unfold AbsoluteCon.
    assert (H3 : ∃ absu, absu = {` λ k v, v = Abs[u[k]] `}).
    { exists {` λ k v, v = Abs[u[k]] `}; reflexivity. }
    destruct H3 as [absu H3]. rewrite <- H3.
    assert (H4 : IsSeq absu ).
    { rewrite H3. split.
      - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2. assumption.
      - apply AxiomI. intro k; split; intro I1; apply AxiomII;
        applyAxiomII I1; auto.
        exists (Abs[u[k]]).
        apply AxiomII'. reflexivity. }
    assert (H5 : ∀ k, absu[k] = Abs[u[k]]).
    { intro k. apply f_x; try apply H4. rewrite H3.
      apply AxiomII'. reflexivity. }
    assert (H20 : ∀ a k, a <> 0 -> pow a k <> 0).
    { intros a k J1. induction k as [|k IHk].
      - simpl. lra.
      - simpl. apply Rmult_integral_contrapositive_currified; auto. }
    assert (H7 : ∀ n : nat,0 < absu [n]).
    { intro n. rewrite H5. rewrite H2.
      apply Abs_not_eq_0.
      assert (I1 : / INR (S (2 * n) !) <> 0).
      { apply Rinv_neq_0_compat. apply Rgt_not_eq. apply H9. }
      apply Rmult_integral_contrapositive_currified; auto.
      apply Rmult_integral_contrapositive_currified.
      - apply H20. lra.
      - apply H20. assumption. }
    apply Theorem12_7_3; auto. exists 0. split; try lra.
    assert (H8 : ∃ u', u' = {` λ n v, v = absu [S n] / absu [n] `}).
    { exists {` λ n v, v = absu [S n] / absu [n] `}; reflexivity. }
    destruct H8 as [u' H8].
    rewrite <- H8. assert (H10 : IsSeq u').
    { rewrite H8. split.
      - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
        rewrite I2. assumption.
      - apply AxiomI. intro k; split; intro I1; apply AxiomII;
        applyAxiomII I1; auto.
        exists (absu [S k] / absu [k]).
        apply AxiomII'. reflexivity. }
    assert (H11 : ∀ k, u'[k] = absu [S k] / absu [k]).
    { intro k. apply f_x; try apply H10. rewrite H8.
      apply AxiomII'. reflexivity. }
    split; auto. intros ε H12.
    assert (H13 : 0 < x * x).
    { apply Rdichotomy in H6. destruct H6 as [H6 | H6].
      - apply Ropp_0_gt_lt_contravar in H6.
        assert (I1 : x * x = (-x) * (-x)). field.
        rewrite I1. apply Rmult_lt_0_compat; auto.
      - apply Rmult_lt_0_compat; auto. }
    generalize (Archimedes ε (x * x) H12 H13).
    intros [N H14]. exists N. intros n H15.
    assert (H16 : 0 < u'[n]).
    { rewrite H11. apply Rdiv_lt_0_compat; apply H7. }
    rewrite Rminus_0_r. rewrite Abs_gt; auto.
    rewrite H11. rewrite H5. rewrite H5.
    assert (H17 : ∀ k, u[k] <> 0).
    { intros k I1. generalize (H7 k). intro I2.
      apply Rlt_not_eq in I2. apply I2.
      rewrite H5. rewrite I1. rewrite Abs_ge; lra. }
    rewrite <- Abs_div; auto.
    assert (H18 : ∀ a k, a <> 0 -> (pow a (S k)) / (pow a k) = a).
    { intros a k I1. simpl. field. apply H20; assumption. }
    rewrite H2. rewrite H2.
    assert (H19 : pow (-1) (S n) * pow x (S (2 * S n))
      / INR (S (2 * S n) !) / (pow (-1) n * pow x (S (2 * n))
      / INR (S (2 * n) !)) = pow (-1) (S n) / pow (-1) n
      * (pow x (S (2 * S n)) / pow x (S (2 * n)))
      / (INR (S (2 * S n) !) / INR (S (2 * n) !)) ).
    { field. repeat split.
      - apply Rgt_not_eq. apply lt_0_INR.
        apply Lemma6_3_1.
      - apply H20. assumption.
      - apply H20; lra.
      - apply Rgt_not_eq. apply lt_0_INR.
        apply Lemma6_3_1. }
    rewrite H19; clear H19.
    rewrite H18; try lra.
    assert (H19 : S (2 * S n) = S (S (S (2 * n)))).
    { simpl. rewrite Nat.add_succ_r. reflexivity. }
    assert (H21 : pow x (S (2 * S n)) / pow x (S (2 * n)) = x * x).
    { rewrite H19. simpl. field. split; auto. }
    rewrite H21. clear H21. rewrite H19.
    assert (H21 : S (S (S (2 * n))) ! =
      ((S (S (S (2 * n)))) * (S (S (2 * n))) * S (2 * n) !)%nat).
    { assert (I1 : ∀ k, (S k)! = ((S k) * k!)%nat).
      { intro k. simpl. reflexivity. }
      rewrite I1. rewrite I1. apply Nat.mul_assoc. }
    rewrite H21. clear H21. rewrite mult_INR.
    assert (H21 : INR (S (S (S (2 * n))) *
      S (S (2 * n))) * INR (S (2 * n) !) /
      INR (S (2 * n) !) = INR (S (S (S (2 * n))) *
      S (S (2 * n)))).
    { field. apply not_0_INR. apply Nat.neq_sym.
      apply lt_0_neq. apply Lemma6_3_1. }
    rewrite H21. clear H21.
    assert (H21 : 0 < INR (S (S (S (2 * n))) *
      S (S (2 * n)))).
    { apply lt_0_INR. apply Nat.mul_pos_pos; apply Nat.lt_0_succ. }
    rewrite Abs_div; try apply Rgt_not_eq; auto.
    rewrite Abs_mult. rewrite Abs_lt; try lra.
    rewrite Abs_gt; try lra. rewrite Abs_gt; try lra.
    assert (H22 : - -1 * (x * x) = x * x). field.
    rewrite H22. clear H22.
    assert (H22 : INR n < INR (S (S (S (2 * n))) * S (S (2 * n)))).
    { apply lt_INR. pattern n at 1. rewrite <- Nat.mul_1_r.
      apply Nat.mul_lt_mono.
      - simpl. apply Nat.lt_lt_succ_r. apply Nat.lt_lt_succ_r.
        apply le_lt_n_Sm. apply Nat.le_add_r.
      - apply lt_n_S. apply Nat.lt_0_succ. }
    assert (H23 : 0 < INR n).
    { apply lt_0_INR. apply Nat.lt_lt_0 with (n := N). assumption. }
    apply Rmult_gt_reg_l with
      (r := INR (S (S (S (2 * n))) * S (S (2 * n)))); try lra.
    assert (H24 : INR (S (S (S (2 * n))) * S (S (2 * n))) *
      (x * x / INR (S (S (S (2 * n))) * S (S (2 * n)))) = x * x).
    field; try lra. rewrite H24. clear H24.
    apply Rmult_lt_compat_r with (r := ε) in H22; auto.
    apply Rlt_trans with (r2 := INR n * ε); auto.
    apply lt_INR in H15.
    apply Rmult_lt_compat_r with (r := ε) in H15; auto.
    lra.
Qed.

(* 定义正弦函数 *)
Definition sin := {` λ x y, limit_seq (Series {` λ k v,
    v = (-1)^^k * x^^(S (2*k)%nat)
    / INR ((S (2*k)%nat)!) `}) y `}.

(* 定理: sin是一个函数 *)
Theorem sin_function : Function sin.
Proof.
  intros x y z H0 H1. applyAxiomII' H0. applyAxiomII' H1.
  eapply Theorem2_2; eauto.
Qed.

(* 定理: sin的定义域为全体实数 *)
Theorem sin_dom : dom[sin] = Full R.
Proof.
  apply AxiomI. intro x; split; intro H0;
  apply AxiomII; applyAxiomII H0; auto.
  generalize (SinSeries x). intros [y H1].
  exists y. apply AxiomII'. assumption.
Qed.

Theorem sin_value : ∀ x, limit_seq (Series {` λ k v,
    v = (-1)^^k * x^^(S (2*k)%nat)
    / INR ((S (2*k)%nat)!) `}) sin[x].
Proof.
  intro x. assert (H0 : x ∈ dom[sin]).
  { rewrite sin_dom. apply AxiomII. reflexivity. }
  apply x_fx in H0; try apply sin_function.
  applyAxiomII' H0. assumption.
Qed.

Lemma pow_2 : ∀ x k, x^^(2*k) = (x*x)^^k.
Proof.
  intros x k. induction k as [|k IHk].
  - simpl. reflexivity.
  - assert (H0 : (2 * S k = S (S (2 * k)))%nat).
    { simpl. rewrite Nat.add_succ_r. reflexivity. }
    rewrite H0. simpl. simpl in IHk. rewrite IHk.
    rewrite Rmult_assoc. reflexivity.
Qed.

(* 定理: (sin x) / x 当x趋向于0时，极限为1 (利用函数极限的迫敛性证明) *)
Theorem sin_div_x : limit {` λ x y, x <> 0 /\ y = sin[x] / x `} 0 1.
Proof.
  assert (H0 : ∃ g, g = {` λ x y, limit_seq (Series {` λ k v,
    v = 1 * (x*x)^^k `}) y `}).
  { exists {` λ x y, limit_seq (Series {` λ k v,
      v = 1 * (x*x)^^k `}) y `}; reflexivity. }
  destruct H0 as [g H0].
  assert (H1 : ∃ f, f = {` λ x y, limit_seq (Series {` λ k v,
    (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * (x*x)^^k) `}) y `}).
  { exists {` λ x y, limit_seq (Series {` λ k v,
    (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * (x*x)^^k) `}) y `};
    reflexivity. }
  destruct H1 as [f H1].
  assert (H2 : ∃ h, h = {` λ x y, x <> 0 /\ y = sin[x] / x `}).
  { exists {` λ x y, x <> 0 /\ y = sin[x] / x `}; reflexivity. }
  destruct H2 as [h H2].
  assert (H3 : Function h).
  { rewrite H2.
    intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    destruct I2 as [I2 I3]. rewrite I3. apply I1. }
  assert (H4 : Function g).
  { rewrite H0.
    intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    eapply Theorem2_2; eauto. }
  assert (H5 : Function f).
  { rewrite H1.
    intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    eapply Theorem2_2; eauto. }
  assert (H6 : ∀ x, IsSeq {` λ k v, v = 1 * (x*x)^^k `}).
  { intro x. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists (1 * pow (x * x) k).
      apply AxiomII'. reflexivity. }
  assert (H7 : ∀ x, IsSeq {` λ k v, (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * (x*x)^^k) `}).
  { intro x. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      destruct I1 as [I1 | I1].
      + destruct I2 as [I2 | I2].
        * destruct I2 as [I2 I3]. rewrite I3. apply I1.
        * exfalso. destruct I2 as [I2 I3].
          destruct I1 as [I1 I4]. apply lt_0_neq in I2.
          apply I2. rewrite I1. reflexivity.
      + destruct I2 as [I2 | I2].
        * exfalso. destruct I2 as [I2 I3].
          destruct I1 as [I1 I4]. apply lt_0_neq in I1.
          apply I1. rewrite I2. reflexivity.
        * destruct I2 as [I2 I3]. rewrite I3. apply I1.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      destruct classic with (P := k = 0%nat) as [I2 | I2].
      + exists 1. apply AxiomII'. left. auto.
      + apply Nat.neq_sym in I2. apply neq_0_lt in I2.
        exists (- 1 * pow (x * x) k). apply AxiomII'.
        right. auto. }
  assert (H8 : ∀ x n, {` λ k v, v = 1 * pow (x * x) k `} [n]
    = 1 * (x*x)^^n).
  { intros x n. apply f_x; try apply H6.
    apply AxiomII'. reflexivity. }
  assert (H9 : ∀ x, IsSeq {` λ k v, v = - 1 * (x*x)^^k `}).
  { intro x. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists (- 1 * pow (x * x) k).
      apply AxiomII'. reflexivity. }
  assert (H10 : ∀ x n, {` λ k v, v = - 1 * (x*x)^^k `} [n]
    = - 1 * (x*x)^^n).
  { intros x n. apply f_x; try apply H9.
    apply AxiomII'. reflexivity. }
  assert (H11 : ∀ x, IsSeq {` λ k v,
    v = (pow (-1) k) * (pow x ((2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `}).
  { intro x. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists ((pow (-1) k) * (pow x ((2 * k)%nat))
        / INR ((S (2 * k)%nat)!)).
      apply AxiomII'. reflexivity. }
  assert (H12 : ∀ x n, {` λ k v, v =
    (pow (-1) k) * (pow x ((2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `} [n]
    = (pow (-1) n) * (pow x ((2 * n)%nat))
    / INR ((S (2 * n)%nat)!)).
  { intros x n. apply f_x; try apply H11.
    apply AxiomII'. reflexivity. }
  assert (H13 : ∀ x, IsSeq {` λ k v,
    v = (pow (-1) k) * (pow x (S (2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `}).
  { intro x. split.
    - intros x0 y0 z0 I1 I2. applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption.
    - apply AxiomI. intro k; split; intro I1; apply AxiomII;
      applyAxiomII I1; auto.
      exists ((pow (-1) k) * (pow x (S (2 * k)%nat))
        / INR ((S (2 * k)%nat)!)).
      apply AxiomII'. reflexivity. }
  assert (H14 : ∀ x n, {` λ k v, v =
    (pow (-1) k) * (pow x (S (2 * k)%nat))
    / INR ((S (2 * k)%nat)!) `} [n]
    = (pow (-1) n) * (pow x (S (2 * n)%nat))
    / INR ((S (2 * n)%nat)!)).
  { intros x n. apply f_x; try apply H13.
    apply AxiomII'. reflexivity. }
  assert (H15 : ∀ x, x <> 0 -> limit_seq (Series {` λ k v,
    v = (-1)^^k * x^^((2*k)%nat)
    / INR ((S (2*k)%nat)!) `}) (sin[x] / x)).
  { intros x I1.
    generalize (SeriesSeq {` λ k v, v = (-1) ^^ k *
      x ^^ (2 * k) / INR ((S (2 * k)) !) `}); intros I2.
    split; auto.
    intros ε I3. generalize (sin_value x); intros [I4 I5].
    assert (I6 : 0 < ε * Abs[x]).
    { apply Rmult_lt_0_compat; auto.
      apply Abs_not_eq_0. assumption. }
    apply I5 in I6 as I7. destruct I7 as [N I7].
    exists N. intros n I8. rewrite SeriesValue; auto.
    apply I7 in I8 as I9. rewrite SeriesValue in I9; auto.
    assert (I10 : ∀ m, Σ {` λ k v, v =
      (pow (-1) k) * (pow x ((2 * k)%nat))
      / INR ((S (2 * k)%nat)!) `} m =
      (Σ {` λ k v,
      v = (pow (-1) k) * (pow x (S (2 * k)%nat))
      / INR ((S (2 * k)%nat)!) `} m) / x).
    { intro m. induction m as [|m IHm].
      - simpl. rewrite H12. simpl in H14. rewrite H14.
        simpl. field. assumption.
      - simpl. simpl in IHm. rewrite IHm. rewrite Rdiv_plus_distr.
        apply Rplus_eq_compat_l. simpl in H12.
        rewrite H12. simpl in H14. rewrite H14.
        field. split; auto.
        assert (J1 : INR ((S (2 * (S m))%nat)!) <> 0).
        { apply not_0_INR. apply Nat.neq_sym. apply lt_0_neq.
          apply Lemma6_3_1. }
        simpl in J1. simpl. assumption. }
    rewrite I10. rewrite <- Rdiv_minus_distr.
    rewrite Abs_div; auto. apply Abs_not_eq_0 in I1.
    apply Rmult_lt_reg_r with (r := Abs[x]); auto.
    assert (I11 : Abs[Σ {` λ k v, v =
      (pow (-1) k) * (pow x (S (2 * k)%nat))
      / INR ((S (2 * k)%nat)!) `} n - sin[x]] / Abs[x] * Abs[x]
      = Abs[Σ {` λ k v, v =
      (pow (-1) k) * (pow x (S (2 * k)%nat))
      / INR ((S (2 * k)%nat)!) `} n - sin[x]]).
    { field. apply Rgt_not_eq. assumption. }
    rewrite I11. assumption. }
  assert (H16 : \{ λ x, -1 < x < 1 \} ⊂ dom[g]).
  { intros x I1. applyAxiomII I1. apply AxiomII.
    exists (1 / (1 - x * x)). rewrite H0. apply AxiomII'.
    apply SeriesProportionalSequence.
    destruct (Rlt_or_le x 0) as [I2 | I2].
    - apply Ropp_0_gt_lt_contravar in I2 as I4.
      assert (I3 : x * x = (-x) * (-x)). field.
      rewrite I3. split.
      + generalize (Rmult_lt_0_compat (-x) (-x) I4 I4).
        lra.
      + assert (I5 : 1 = 1 * 1). field. rewrite I5.
        apply Rmult_gt_0_lt_compat; lra.
    - split.
      + generalize (Rmult_le_pos x x I2 I2). lra.
      + assert (I5 : 1 = 1 * 1). field. rewrite I5.
        apply Rmult_le_0_lt_compat; lra. }
  assert (H17 : IsSeq {` λ k1 v1, v1 = 2 `}).
  { split.
    - intros x0 y0 z0 J1 J2. applyAxiomII' J1; applyAxiomII' J2.
      rewrite J2. assumption.
    - apply AxiomI. intro z; split; intro J1; apply AxiomII;
      applyAxiomII J1; auto.
      exists (2).
      apply AxiomII'. reflexivity. }
  assert (H18 : ∀ (k : nat), {` λ k1 v1, v1 = 2 `} [k] = 2).
  { intro k1. apply f_x; try apply H17.
    apply AxiomII'. reflexivity. }
  assert (H19 : ∀ x, (Series {` λ k v,
    (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * pow (x * x) k) `})
    = {` λ k v, v = {` λ k1 v1, v1 = 2 `} [k] + 
      (Series {` λ k2 v2, v2 = - 1 * pow (x * x) k2 `}) [k] `} ).
  { intro x. apply AxiomI. intros [k v].
    assert (I3 : ∀ m, Σ {` λ k v, (k = 0%nat /\ v = 1) \/
      ((0 < k)%nat /\ v = - 1 * pow (x * x) k) `} m =
      2 + Σ {` λ k2 v2, v2 = - 1 * pow (x * x) k2 `} m).
    { intro m. induction m as [|m IHm].
      - simpl. rewrite H10.
        assert (J1 : {` λ k v, (k = 0%nat /\ v = 1) \/
          ((0 < k)%nat /\ v = - 1 * pow (x * x) k) `} [0%nat] = 1).
        { apply f_x; try apply H7. apply AxiomII'. left.
          split; reflexivity. }
        rewrite J1. simpl. field.
      - simpl. rewrite <- Rplus_assoc. rewrite <- IHm.
        apply Rplus_eq_compat_l. rewrite H10.
        apply f_x; try apply H7. apply AxiomII'. right.
        split; auto. apply Nat.lt_0_succ. }
    split; intro I4; apply AxiomII'; applyAxiomII' I4.
    - rewrite H18. rewrite SeriesValue; auto. rewrite I4.
      clear I4. apply I3.
    - rewrite H18 in I4. rewrite SeriesValue in I4; auto.
      rewrite I3. assumption. }
  assert (H20 : ∀ x, -1 < x < 1 -> -1 < x * x < 1).
  { intros x I1. destruct (Rlt_or_le x 0) as [I2 | I2].
    - apply Ropp_0_gt_lt_contravar in I2 as I4.
      assert (I3 : x * x = (-x) * (-x)). field.
      rewrite I3. split.
      + generalize (Rmult_lt_0_compat (-x) (-x) I4 I4).
        lra.
      + assert (I5 : 1 = 1 * 1). field. rewrite I5.
        apply Rmult_gt_0_lt_compat; lra.
    - split.
      + generalize (Rmult_le_pos x x I2 I2). lra.
      + assert (I5 : 1 = 1 * 1). field. rewrite I5.
        apply Rmult_le_0_lt_compat; lra. }
  assert (H21 : \{ λ x, -1 < x < 1 \} ⊂ dom[f]).
  { intros x I1. applyAxiomII I1. apply AxiomII.
    exists (2 + (-1) / (1 - x * x)). rewrite H1.
    apply AxiomII'. rewrite H19. apply Theorem2_7_1'.
    - split; auto. intros ε I2. exists 0%nat.
      intros n I3. rewrite H18. rewrite Abs_ge; lra.
    - apply SeriesProportionalSequence.
      auto. }
  assert (H22 : limit g 0 1).
  { unfold limit. split; auto. exists 1. repeat split.
    - lra.
    - intros x I1. applyAxiomII I1. apply H16.
      apply AxiomII. rewrite Rminus_0_r in I1.
      destruct (Rlt_or_le x 0) as [I2 | I2].
      + rewrite Abs_lt in I1; auto. lra.
      + apply Rle_ge in I2. rewrite Abs_ge in I1; auto.
        lra.
    - intros ε I1. exists (ε / (1 + ε)).
      assert (I4 : 0 < ε / (1 + ε) < 1).
      { split.
        * apply Rdiv_lt_0_compat; lra.
        * apply Rmult_lt_reg_r with (r := 1 + ε); try lra.
          assert (J1 : ε / (1 + ε) * (1 + ε) = ε).
          { field. lra. }
          rewrite J1. lra. }
      split; auto. intros x I2. rewrite Rminus_0_r in I2.
      assert (I3 : 0 < Abs[x] < 1). lra.
      assert (I5 : -1 < x < 1).
      { destruct (Rlt_or_le x 0) as [J2 | J2].
        - rewrite Abs_lt in I3; auto. lra.
        - apply Rle_ge in J2. rewrite Abs_ge in I3; auto.
          lra. }
      assert (I6 : g[x] = 1 / (1 - x *x)).
      { apply f_x; auto. rewrite H0. apply AxiomII'.
        apply SeriesProportionalSequence. apply H20.
        auto. }
      assert (I7 : 0 < x * x < 1).
      { destruct (Rlt_or_le x 0) as [J1 | J1].
        - apply Ropp_0_gt_lt_contravar in J1 as J2.
          assert (J3 : x * x = (-x) * (-x)). field.
          rewrite J3. split.
          + apply Rmult_lt_0_compat; auto.
          + assert (J4 : 1 = 1 * 1). field. rewrite J4.
            apply Rmult_gt_0_lt_compat; lra.
        - split.
          + apply Rle_ge in J1 as J2. rewrite Abs_ge in I3; auto.
            apply Rmult_lt_0_compat; apply I3.
          + assert (J2 : 1 = 1 * 1). field. rewrite J2.
            apply Rmult_le_0_lt_compat; lra. }
      assert (I8 : 0 < g[x] - 1).
      { assert (J1 : g[x] - 1 = x * x / (1 - x * x)).
        { rewrite I6. field. lra. }
        rewrite J1. apply Rdiv_lt_0_compat; lra. }
      rewrite Abs_gt; auto. rewrite I6.
      apply Rplus_lt_reg_l with (r := 1).
      assert (I9 : 1 + (1 / (1 - x * x) - 1)
        = 1 / (1 - x * x)). field; lra.
      rewrite I9. clear I9.
      rewrite <- (Rinv_involutive (1 + ε)); try lra.
      unfold Rdiv. rewrite Rmult_1_l.
      assert (I9 : 0 < / (1 + ε) * (1 - x * x)).
      { apply Rmult_lt_0_compat; try lra.
        apply Rinv_0_lt_compat. lra. }
      apply Rinv_lt_contravar; auto.
      assert (I10 : x * x < 1 - / (1 + ε)).
      { assert (J1 : 1 - / (1 + ε) = ε / (1 + ε)).
        { field. lra. }
        rewrite J1.
        assert (J2 : x * x <= Abs[x]).
        { destruct (Rlt_or_le x 0) as [J3 | J3].
          - apply Ropp_0_gt_lt_contravar in J3 as J4.
            assert (J5 : x * x = (-x) * (-x)). field.
            rewrite J5. rewrite Abs_lt in *; auto.
            pattern (-x) at 3. rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; lra.
          - apply Rle_ge in J3 as J4.
            rewrite Abs_ge in *; auto.
            pattern (x) at 3. rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; lra. }
        lra. }
      lra. }
  assert (H23 : limit f 0 1).
  { unfold limit. split; auto. exists 1. repeat split.
    - lra.
    - intros x I1. applyAxiomII I1. apply H21.
      apply AxiomII. rewrite Rminus_0_r in I1.
      destruct (Rlt_or_le x 0) as [I2 | I2].
      + rewrite Abs_lt in I1; auto. lra.
      + apply Rle_ge in I2. rewrite Abs_ge in I1; auto.
        lra.
    - intros ε I1. exists (ε / (1 + ε)).
      assert (I4 : 0 < ε / (1 + ε) < 1).
      { split.
        * apply Rdiv_lt_0_compat; lra.
        * apply Rmult_lt_reg_r with (r := 1 + ε); try lra.
          assert (J1 : ε / (1 + ε) * (1 + ε) = ε).
          { field. lra. }
          rewrite J1. lra. }
      split; auto. intros x I2. rewrite Rminus_0_r in I2.
      assert (I3 : 0 < Abs[x] < 1). lra.
      assert (I5 : -1 < x < 1).
      { destruct (Rlt_or_le x 0) as [J2 | J2].
        - rewrite Abs_lt in I3; auto. lra.
        - apply Rle_ge in J2. rewrite Abs_ge in I3; auto.
          lra. }
      assert (I6 : f[x] = 2 + (- 1) / (1 - x*x)).
      { apply f_x; auto. rewrite H1. apply AxiomII'.
        rewrite H19. apply Theorem2_7_1'.
        - split; auto. intros ε' J1. exists 0%nat.
          intros n J2. rewrite H18. rewrite Abs_ge; lra.
        - apply SeriesProportionalSequence. apply H20.
          auto. }
      assert (I7 : 0 < x * x < 1).
      { destruct (Rlt_or_le x 0) as [J1 | J1].
        - apply Ropp_0_gt_lt_contravar in J1 as J2.
          assert (J3 : x * x = (-x) * (-x)). field.
          rewrite J3. split.
          + apply Rmult_lt_0_compat; auto.
          + assert (J4 : 1 = 1 * 1). field. rewrite J4.
            apply Rmult_gt_0_lt_compat; lra.
        - split.
          + apply Rle_ge in J1 as J2. rewrite Abs_ge in I3; auto.
            apply Rmult_lt_0_compat; apply I3.
          + assert (J2 : 1 = 1 * 1). field. rewrite J2.
            apply Rmult_le_0_lt_compat; lra. }
      assert (I8 : f[x] - 1 < 0).
      { assert (J1 : f[x] - 1 = - (x * x / (1 - x * x))).
        { rewrite I6. field. lra. }
        rewrite J1. apply Ropp_lt_gt_0_contravar.
        apply Rdiv_lt_0_compat; lra. }
      rewrite Abs_lt; auto. rewrite I6.
      apply Rplus_lt_reg_l with (r := 1).
      assert (I9 : 1 + - (2 + -1 / (1 - x * x) - 1)
        = 1 / (1 - x * x)). field; lra.
      rewrite I9. clear I9.
      rewrite <- (Rinv_involutive (1 + ε)); try lra.
      unfold Rdiv. rewrite Rmult_1_l.
      assert (I9 : 0 < / (1 + ε) * (1 - x * x)).
      { apply Rmult_lt_0_compat; try lra.
        apply Rinv_0_lt_compat. lra. }
      apply Rinv_lt_contravar; auto.
      assert (I10 : x * x < 1 - / (1 + ε)).
      { assert (J1 : 1 - / (1 + ε) = ε / (1 + ε)).
        { field. lra. }
        rewrite J1.
        assert (J2 : x * x <= Abs[x]).
        { destruct (Rlt_or_le x 0) as [J3 | J3].
          - apply Ropp_0_gt_lt_contravar in J3 as J4.
            assert (J5 : x * x = (-x) * (-x)). field.
            rewrite J5. rewrite Abs_lt in *; auto.
            pattern (-x) at 3. rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; lra.
          - apply Rle_ge in J3 as J4.
            rewrite Abs_ge in *; auto.
            pattern (x) at 3. rewrite <- Rmult_1_r.
            apply Rmult_le_compat_l; lra. }
        lra. }
      lra. }
  assert (H24 : Function {` λ x y, x <> 0 /\ y = sin[x] / x `}).
  { intros x y z I1 I2. applyAxiomII' I1; applyAxiomII' I2.
    destruct I2 as [I2 I3]. rewrite I3. apply I1. }
  apply (Theorem3_6 f g); auto.
  exists 1.
  assert (H25 : Neighbor0 0 1 ⊂
    dom[{` λ x y, x <> 0 /\ y = sin[x] / x `}]).
  { intros x I1. applyAxiomII I1. apply AxiomII.
    exists (sin[x] / x). apply AxiomII'. split; auto.
    destruct (Rlt_or_le x 0) as [I2 | I2].
    - lra.
    - apply Rle_ge in I2. rewrite Rminus_0_r in I1.
      rewrite Abs_ge in I1; auto. lra. }
  split; [lra | split]; auto. intros x H26.
  applyAxiomII H26. rewrite Rminus_0_r in H26.
  assert (H27 : -1 < x < 0 \/ 0 < x < 1).
  { destruct (Rlt_or_le x 0) as [I1 | I1].
    - rewrite Abs_lt in H26; auto. left; lra.
    - apply Rle_ge in I1. rewrite Abs_ge in H26; auto. }
  assert (H28 : x <> 0). lra.
  assert (H29 : {` λ x0 y, x0 <> 0 /\ y = sin[x0] / x0`} [x]
    = sin[x] / x).
  { apply f_x; auto. apply AxiomII'. split; auto. }
  rewrite H29. generalize (H15 x H28). intro H30.
  apply lim_a in H30 as H31.
  assert (H32 : ∃ u1, u1 = {` λ(k : nat)(v : R),
    v = pow (-1) k * pow x (2 * k) / INR (S (2 * k) !) `}).
  { exists {` λ(k : nat)(v : R),
      v = pow (-1) k * pow x (2 * k) / INR (S (2 * k) !) `}; auto. }
  destruct H32 as [u1 H32]. rewrite <- H32 in *.
  assert (H33 : ∃ u0, u0 = {` λ k v, (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * pow (x * x) k) `}).
  { exists {` λ k v, (k = 0%nat /\ v = 1) \/
    ((0 < k)%nat /\ v = - 1 * pow (x * x) k) `}; reflexivity. }
  destruct H33 as [u0 H33].
  assert (H34 : ∃ u2, u2 = {` λ k v, v = 1 * (pow (x * x) k) `}).
  { exists {` λ k v, v = 1 * (pow (x * x) k) `}; reflexivity. }
  destruct H34 as [u2 H34].
  generalize (H11 x). intro H35. rewrite <- H32 in H35.
  generalize (H7 x). intro H36. rewrite <- H33 in H36.
  generalize (H6 x). intro H37. rewrite <- H34 in H37.
  assert (H38 : ∀ n, pow (-1) n = 1 \/ pow (-1) n = -1).
  { intro n. induction n as [|n IHn].
    - left. simpl. reflexivity.
    - destruct IHn as [IHn | IHn].
      + right. simpl. rewrite IHn. field.
      + left. simpl. rewrite IHn. field. }
  assert (H39 : 0 < x * x < 1).
  { destruct H27 as [H27 | H27].
    - destruct H27 as [J1 J2].
      apply Ropp_0_gt_lt_contravar in J2 as J3.
      assert (J4 : x * x = (-x) * (-x)). field.
      rewrite J4. split.
      + apply Rmult_lt_0_compat; auto.
      + assert (J5 : 1 = 1 * 1). field. rewrite J5.
        apply Rmult_gt_0_lt_compat; lra.
    - destruct H27 as [J1 J2].
      split.
      + apply Rmult_lt_0_compat; apply J1.
      + assert (J3 : 1 = 1 * 1). field. rewrite J3.
        apply Rmult_le_0_lt_compat; lra. }
  assert (H40 : ∀ n, 0 < pow (x * x) n).
  { intro n. induction n as [|n IHn].
    - simpl. lra.
    - simpl. apply Rmult_lt_0_compat; auto. apply H39. }
  split.
  - assert (I1 : [x, f[x]] ∈ f).
    { apply x_fx; auto. apply H21. apply AxiomII. lra. }
    pattern f at 2 in I1. rewrite H1 in I1.
    applyAxiomII' I1. rewrite <- H33 in I1.
    apply lim_a in I1 as I2.
    rewrite <- I2. rewrite <- H31. apply Theorem2_5.
    + exists f[x]. auto.
    + exists (sin[x] / x); auto.
    + exists 0%nat. intros n I3. clear I3.
      induction n as [|n IHn].
      * rewrite SeriesValue; auto. rewrite SeriesValue; auto.
        simpl. rewrite H33. rewrite H32. rewrite H12.
        assert (I3 : {` λ k v, k = 0%nat /\ v = 1
          \/ (0 < k)%nat /\ v = -1 * pow (x * x) k `} [0%nat] = 1).
        { apply f_x; try apply H7. apply AxiomII'.
          left. split; reflexivity. }
        rewrite I3. simpl. lra.
      * rewrite SeriesValue; auto. rewrite SeriesValue; auto.
        simpl. rewrite SeriesValue in IHn; auto.
        rewrite SeriesValue in IHn; auto.
        apply Rplus_le_compat; auto. rewrite H32.
        rewrite H12.
        assert (I3 : u0[S n] = -1 * pow (x * x) (S n)).
        { apply f_x; try apply H36. rewrite H33.
          apply AxiomII'. right. split; auto.
          apply Nat.lt_0_succ. }
        rewrite I3. rewrite pow_2. generalize (H38 (S n)).
        intro I4. destruct I4 as [I4 | I4].
        -- rewrite I4. apply Rle_trans with (r2 := 0).
          ++ left. assert (I5 : -1 * pow (x * x) (S n)
            = - pow (x * x) (S n)).
            field. rewrite I5. apply Ropp_lt_gt_0_contravar.
            apply H40.
          ++ left. apply Rdiv_lt_0_compat.
            ** generalize (H40 (S n)). intro I5. lra.
            ** generalize (factorial_lt_0_r (S (2 * S n)));
              intro I5. lra.
        -- rewrite I4. assert (I5 : -1 * pow (x * x) (S n)
             = - (pow (x * x) (S n) * (/ 1))). 
           field. rewrite I5.
           assert (I6 : - (pow (x * x) (S n) * (/ 1)) / INR (S (2 * S n) !)
             = - (pow (x * x) (S n) / INR (S (2 * S n) !))).
           { field. generalize (factorial_lt_0_r (S (2 * S n)));
             intro I6. lra. }
           rewrite I6. apply Ropp_le_contravar. unfold Rdiv.
           apply Rmult_le_compat_l.
           ++ left. apply H40.
           ++ apply Rinv_le_contravar; [lra | apply factorial_lt_0_r].
  - assert (I1 : [x, g[x]] ∈ g).
    { apply x_fx; auto. apply H16. apply AxiomII. lra. }
    pattern g at 2 in I1. rewrite H0 in I1.
    applyAxiomII' I1. rewrite <- H34 in I1.
    apply lim_a in I1 as I2.
    rewrite <- I2. rewrite <- H31. apply Theorem2_5.
    + exists (sin[x] / x); auto.
    + exists g[x]. auto.
    + exists 0%nat. intros n I3. clear I3.
      induction n as [|n IHn].
      * rewrite SeriesValue; auto. rewrite SeriesValue; auto.
        simpl. rewrite H34. rewrite H32. rewrite H12.
        assert (I3 : {` λ k v, v = 1 * pow (x * x) k `} [0%nat] = 1).
        { apply f_x; try apply H6. apply AxiomII'. simpl. field. }
        rewrite I3. simpl. lra.
      * rewrite SeriesValue; auto. rewrite SeriesValue; auto.
        simpl. rewrite SeriesValue in IHn; auto.
        rewrite SeriesValue in IHn; auto.
        apply Rplus_le_compat; auto. rewrite H32.
        rewrite H12.
        assert (I3 : u2[S n] = 1 * pow (x * x) (S n)).
        { apply f_x; try apply H37. rewrite H34.
          apply AxiomII'. reflexivity. }
        rewrite I3. rewrite pow_2. generalize (H38 (S n)).
        intro I4. destruct I4 as [I4 | I4].
        -- rewrite I4. unfold Rdiv.
          rewrite Rmult_1_l.
          assert (I5 : pow (x * x) (S n) = pow (x * x) (S n) * / 1).
          field. pattern (pow (x * x) (S n)) at 2.
          rewrite I5. apply Rmult_le_compat_l.
          ++ left. apply H40.
          ++ apply Rinv_le_contravar; [lra | apply factorial_lt_0_r].
        -- rewrite I4. apply Rle_trans with (r2 := 0).
          ++ left. assert (I5 : -1 * pow (x * x) (S n)
              / INR (S (2 * S n) !) = - (pow (x * x) (S n)
              / INR (S (2 * S n) !))).
            { field. generalize (factorial_lt_0_r (S (2 * S n)));
              intro I5. lra. }
            rewrite I5. apply Ropp_lt_gt_0_contravar.
            apply Rdiv_lt_0_compat.
            ** generalize (H40 (S n)). intro I6. lra.
            ** generalize (factorial_lt_0_r (S (2 * S n)));
              intro I6. lra.
          ++ left. rewrite Rmult_1_l. apply H40.
Qed.