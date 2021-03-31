Require Export A_6_2.

Module A6_3.

(* 定义：数列前n项和 *)
Fixpoint Σ (x : Seq) (n : nat) :=
  match n with
  | 0%nat => x[0%nat]
  | S n => Σ x n + x[S n]
  end.

(* 定义: 阶乘 *)
Fixpoint factorial (n : nat) :=
  match n with
  | 0%nat => 1%nat
  | S n => ((S n) * factorial n)%nat
  end.

Notation "n !" := (factorial n)(at level 10).

Lemma Lemma6_3_1 : ∀ n, (0 < n!)%nat.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. apply Nat.lt_0_1.
  - simpl. apply Nat.add_pos_l.
    assumption.
Qed.

Lemma Lemma6_3_2 : ∀ n, n! = mult_NM n n.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn.
    reflexivity.
Qed.

Lemma Lemma6_3_3 : ∀ n, (S n)! = mult_NM (S n) n.
Proof.
  intros n. induction n as [|n IHn].
  - simpl. reflexivity.
  - assert (H0 : ((S (S n)) ! =
      (S (S n)) * (S n)!)%nat).
    { simpl. reflexivity. }
    rewrite H0.
    assert (H1 : (mult_NM (S (S n)) (S n) =
      (S (S n)) * mult_NM (S n) n)%nat).
    { simpl. reflexivity. }
    rewrite H1. rewrite <- IHn.
    reflexivity.
Qed.

Lemma Lemma6_3_4 : ∀ n, (0 < n)%nat -> 0^^n = 0.
Proof.
  intros n H0. destruct n as [|n].
  - apply Nat.lt_irrefl in H0. contradiction.
  - simpl. field.
Qed.

Lemma Lemma6_3_5 : ∀ x n, x <> 0 -> x^^n <> 0.
Proof.
  intros x n. induction n as [|n IHn].
  - intros H0. simpl. lra.
  - intros H0. apply IHn in H0 as H1. simpl.
    apply Rmult_integral_contrapositive_currified; auto.
Qed.

(* 泰勒公式 *)
Theorem Theorem6_9 : ∀ (f : Fun) (n : nat) (x0 : R),
  (0 < n)%nat -> Function f -> x0 ∈ dom[dN f n] ->
    (∃ (o : Fun), InfinitesimalHigherOrder
      o {` λ x y, y = (x - x0)^^n `} x0 /\
      (∀ (x : R), f[x] =
      (Σ {` λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k `} n) + o[x])).
Proof.
  intros f n x0 H0 H1 H2.
  assert (H3 : ∃ Rn, Rn = λ m, {` λ x y,
    y = f[x] - (Σ {` λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k `} m) `}).
  { exists (λ m, {` λ x y, y =
    f[x] - (Σ {` λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k `} m) `}).
    reflexivity. }
  destruct H3 as [Rn H3].
  exists (Rn n). assert (H4 : ∀ m, Function (Rn m)).
  { intros m. rewrite H3. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H5 : ∀ x m, (Rn m)[x] = f[x] -
    (Σ {` λ k v, v = (dN f k)[x0] /
    (INR (k!)) * (x - x0)^^k `} m)).
  { intros x m. apply f_x; auto.
    rewrite H3. apply AxiomII'.
    reflexivity. }
  assert (H6 : ∀ x x0, Function
    {` λ k v, v = (dN f k) [x0]
    / INR (k !) * (x - x0)^^k `}).
  { intros x x2 x1 y1 z1 I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H7 : ∀ x x0 k,
    {` λ k v, v = (dN f k) [x0]
    / INR (k !) * (x - x0)^^k `}[k]
    = (dN f k) [x0] / INR (k !) * (x - x0)^^k).
  { intros x x1 k.
    apply f_x; try apply H6.
    apply AxiomII'. reflexivity. }
  assert (H8 : ∀ m x, (Rn (S m))[x] =
    (Rn m)[x] - (dN f (S m)) [x0] /
    INR ((S m) !) * (x - x0) ^^ (S m)).
  { intros m x.
    rewrite H5. rewrite H5.
    simpl Σ. rewrite H7.
    field. apply not_0_INR.
    apply not_eq_sym. apply lt_0_neq.
    apply Lemma6_3_1. }
  assert (H9 : ∀ k, x0 ∈ dom[dN (Rn k) n]).
  { intros k. induction k as [|k IHk].
    - rewrite H3. assert (I1 : {` λ x y,
        y = f [x] - Σ {` λ k v,
        v = (dN f k) [x0] / INR (k !)
        * (x - x0) ^^ k `} 0 `} =
        {` λ x y, y = f[x] - {` λ x1 y1,
        y1 = f[x0] `}[x] `}).
      { apply AxiomI; intros [x y];
        split; intro I1;
        applyAxiomII' I1; apply AxiomII'.
        - rewrite H7 in I1. simpl in I1.
          rewrite Lemma5_11. simpl.
          rewrite I1. field.
        - simpl. rewrite H7.
          rewrite Lemma5_11 in I1.
          simpl. rewrite I1. field. }
      rewrite I1. clear I1.
      apply AxiomII. exists ((dN f n)[x0] -
        (dN {` λ x1 y1, y1 = f[x0] `} n)[x0]).
      apply Lemma5_13; auto. apply AxiomII.
      exists 0. rewrite Lemma5_14.
      apply AxiomII'. reflexivity. assumption.
    - assert (I1 : Rn (S k) =
        {` λ x y, y = (Rn k)[x] -
        {` λ x1 y1, y1 = (dN f (S k)) [x0]
        / INR ((S k) !) * (x1 - x0) ^^ S k
        `}[x] `}).
      { apply AxiomI. intros [x y].
        split; intro I1.
        - apply AxiomII'.
          apply f_x in I1; auto.
          rewrite <- I1. rewrite Lemma4'.
          apply H8.
        - apply -> AxiomII' in I1.
          lazy beta in I1.
          rewrite Lemma4' in I1.
          rewrite <- H8 in I1.
          rewrite I1. apply x_fx; auto.
          apply AxiomII. rewrite H3.
          exists (f[x] - Σ {` λ k0 v,
            v = (dN f k0) [x0] / INR (k0 !)
            * (x - x0) ^^ k0 `} (S k)).
          apply AxiomII'. reflexivity. }
      rewrite I1. clear I1. apply AxiomII.
      exists ((dN (Rn k) n)[x0] - (dN {` λ x1 y1,
        y1 = (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ S k`} n)[x0]).
      apply Lemma5_13; auto.
      destruct (Nat.le_gt_cases n (S k))
        as [I1 | I1].
      + rewrite Lemma5_7; auto.
        apply AxiomII. exists ((dN f (S k)) [x0]
          / INR ((S k) !) * INR (mult_NM (S k) n)
          * (x0 - x0) ^^ (S k - n)).
        apply AxiomII'. reflexivity.
      + rewrite Lemma5_7'; auto. apply AxiomII.
        exists 0. apply AxiomII'. reflexivity. }
  assert (H10 : ∀ k, Function {` λ x y,
      y = Σ {` λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 `} k `}).
  { intros k. intros x y z I1 I2.
    applyAxiomII' I1; applyAxiomII' I2.
    rewrite I2; assumption. }
  assert (H11 : ∀ k x, {` λ x y, y =
    Σ {` λ k1 v, v = (dN f k1)[x0] /
    (INR (k1!)) * (x - x0)^^k1 `} k `} [x]
    = Σ {` λ k1 v, v = (dN f k1)[x0] /
    (INR (k1!)) * (x - x0)^^k1 `} k).
  { intros k x. apply f_x;
    try apply H10.
    apply AxiomII'. reflexivity. }
  assert (H12 : ∀ x k m, (k < m)%nat ->
      [x, 0] ∈ (dN ({` λ x1 y1,
      y1 = Σ {` λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x1 - x0)^^k1 `} k `}) m)).
  { intros x k m. induction k as [|k IHk].
    - intros I1. simpl.
      assert (I2 : {` λ x y, y = {` λ k1 v,
        v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 `}[0%nat] `} =
        {` λ x y, y = f[x0] `}).
      { apply AxiomI; intros [x1 y1];
        split; intro J1;
        applyAxiomII' J1; apply AxiomII'.
        - rewrite J1. rewrite H7.
          simpl. field.
        - rewrite H7. simpl. rewrite J1.
          field. }
      rewrite I2. clear I2.
      rewrite Lemma5_14; [apply AxiomII' | assumption].
      reflexivity.
    - intros I1. assert (I2 : {` λ x1 y1,
        y1 = Σ {` λ k1 v, v = (dN f k1) [x0]
        / INR (k1 !) * (x1 - x0) ^^ k1 `} (S k) `}
        = {` λ x2 y2, y2 = {` λ x1 y1,
        y1 = Σ {` λ k1 v, v = (dN f k1) [x0]
        / INR (k1 !) * (x1 - x0) ^^ k1 `} k `}[x2]
        + {` λ x1 y1, y1 = (dN f (S k)) [x0]
        / INR ((S k) !) * (x1 - x0) ^^ (S k) `}[x2]
        `} ).
      { apply AxiomI; intros [x1 y1];
        split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H11. rewrite Lemma4'.
          rewrite H7 in J1. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7. rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I2. clear I2. assert (I2 : (k < m)%nat).
      { apply Nat.lt_succ_l; assumption. }
      apply IHk in I2 as I3.
      assert (I4 : (0 < m)%nat).
      { apply (Nat.lt_lt_0 k). assumption. }
      apply f_x in I3 as I5; try apply Lemma5_15; auto.
      assert (I6 : (dN {` λ x1 y1, y1 =
        (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ (S k) `} m)[x] = 0).
      { apply f_x.
        - apply Lemma5_15; assumption.
        - rewrite Lemma5_7'; auto.
          apply AxiomII'. reflexivity. }
      assert (I7 : 0 = (dN {` λ x2 y2,
      y2 = Σ {` λ k1 v, v = (dN f k1) [x0]
      / INR (k1 !) * (x2 - x0) ^^ k1 `}
      k `} m) [x] + (dN {` λ x1 y1, y1 =
        (dN f (S k)) [x0] / INR ((S k) !)
        * (x1 - x0) ^^ (S k) `} m)[x]).
      { rewrite I5. rewrite I6. field. }
      rewrite I7. apply Lemma5_13'.
      + apply AxiomII. exists 0.
        assumption.
      + apply AxiomII. exists 0.
        rewrite Lemma5_7'; auto.
        apply AxiomII'. reflexivity. }
  assert (H13 : ∀ x k, [x, (dN f k)[x0]] ∈
      (dN ({` λ x y,
      y = Σ {` λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 `} k `}) k)).
  { intros x k. destruct k as [|k].
    - simpl. apply AxiomII'.
      rewrite H7. simpl. field.
    - assert (I1 : {` λ x y, y = Σ {` λ k1 v,
        v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 `} (S k) `} =
        {` λ x y, y = {` λ x1 y1, y1 =
          Σ {` λ k1 v,
          v = (dN f k1) [x0] / INR (k1 !)
          * (x1 - x0) ^^ k1 `} k `}[x] +
        {` λ x1 y1, y1 = (dN f (S k)) [x0]
          / INR ((S k) !) * (x1 - x0) ^^ (S k) `}[x]
        `}).
      { apply AxiomI. intros [x1 y1].
        split; intros J1.
        - applyAxiomII' J1. apply AxiomII'.
          rewrite H11. rewrite Lemma4'.
          rewrite H7 in J1. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7. rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I1. clear I1.
      assert (I1 : (k < S k)%nat).
      { apply Nat.lt_succ_diag_r. }
      apply (H12 x) in I1.
      assert (I2 : [x, (dN f (S k)) [x0]]
          ∈ dN {` λ x y, y = (dN f (S k)) [x0]
          / INR ((S k) !) * (x - x0) ^^ (S k)
          `} (S k)).
      { rewrite Lemma5_7; try apply le_n.
        apply AxiomII'. rewrite <- Lemma6_3_2.
        rewrite Nat.sub_diag. simpl pow.
        field. apply not_0_INR.
        apply not_eq_sym. apply lt_0_neq.
        apply Lemma6_3_1. }
      assert (I3 : (dN f (S k)) [x0] = (dN {` λ x y,y =
        Σ {` λ k1 v, v = (dN f k1) [x0] / INR (k1 !)
        * (x - x0) ^^ k1 `} k `} (S k))[x] + 
        (dN {` λ x y, y = (dN f (S k)) [x0]
        / INR ((S k) !) * (x - x0) ^^ S k `}
        (S k))[x]).
      { generalize (Nat.lt_0_succ k). intros J1.
        apply f_x in I1; try apply Lemma5_15; auto.
        apply f_x in I2; try apply Lemma5_15; auto.
        rewrite I1; rewrite I2. field. }
      pattern ((dN f (S k)) [x0]) at 1.
      rewrite I3. apply Lemma5_13'.
      + apply AxiomII. exists 0. assumption.
      + apply AxiomII. exists ((dN f (S k)) [x0]).
        assumption. }
  assert (H14 : ∀ k, (k <= n)%nat ->
    [x0, 0] ∈ (dN (Rn k) k)).
  { intros k I0. assert (I1 : Rn k = {` λ x y,
      y = f[x] - {` λ x1 y1, y1 = Σ {` λ k1 v,
      v = (dN f k1) [x0] / INR (k1 !) *
      (x1 - x0) ^^ k1 `} k `}[x] `}).
    { rewrite H3. apply AxiomI;
      intros [x y]; split; intro J1;
      applyAxiomII' J1; apply AxiomII'.
      - rewrite H11. assumption.
      - rewrite H11 in J1. assumption. }
    rewrite I1. clear I1.
    assert (I1 : x0 ∈ dom[ dN f k]).
    { apply le_lt_or_eq in I0 as [I0 | I0].
      - apply Lemma5_6 with (k := k)
          in H2 as J1; auto.
        destruct J1 as [δ [J1 J2]].
        apply J2. apply AxiomII.
        apply Abs_R; lra.
      - rewrite I0; assumption. }
    assert (I2 : Function (dN f k)).
    { apply Lemma5_16. assumption. }
    apply x_fx in I1 as I3; auto.
    generalize (H13 x0 k); intros I4.
    assert (I5 : 0 = (dN f k)[x0] -
      (dN {` λ x1 y1, y1 = Σ {` λ k1 v,
      v = (dN f k1) [x0] / INR (k1 !) *
      (x1 - x0) ^^ k1 `} k `} k)[x0]).
    { apply f_x in I4.
      - rewrite I4. field.
      - apply Lemma5_16. auto. }
    rewrite I5. apply Lemma5_13; auto.
    apply AxiomII. exists ((dN f k) [x0]).
    assumption. }
  assert (H15 : ∀ k, (k <= n)%nat ->
    [x0, 0] ∈ (dN (Rn n) k)).
  { clear H0.
    induction n as [|n IHn].
    - intros k I1. apply le_n_0_eq in I1.
      rewrite <- I1. simpl. rewrite H3.
      apply AxiomII'. simpl. rewrite H7.
      simpl. field.
    - intros k I1. assert (I2 : x0 ∈ dom[ dN f n]).
      { apply Lemma5_6 with (k := n) in H2 as J1.
        destruct J1 as [δ [J1 J2]]. apply J2.
        - apply AxiomII. apply Abs_R. lra.
        - apply Nat.lt_succ_diag_r. }
      assert (I3 : ∀k : nat,x0 ∈ dom[ dN (Rn k) n]).
      { intros m. generalize (H9 m); intros J1.
        apply Lemma5_6 with (k := n) in J1 as J2.
        destruct J2 as [δ [J2 J3]].
        - apply J3. apply AxiomII.
          apply Abs_R. lra.
        - apply Nat.lt_succ_diag_r. }
      assert (I4 : (∀ k, (k <= n)%nat ->
        [x0, 0] ∈ dN (Rn k) k)).
      { intros k0 J1. apply H14.
        apply le_S. assumption. }
      generalize (IHn I2 I3 I4); intros I5.
      apply Nat.le_succ_r in I1 as [I1 | I1].
      + generalize (I5 k I1); intros I6.
        assert (I7 : Rn (S n) = {` λ x y, y =
          (Rn n)[x] - {` λ x1 y1, y1 =
          (dN f (S n)) [x0] / INR ((S n) !)
          * (x1 - x0) ^^ S n `}[x] `}).
        { apply AxiomI; intros [x y];
          split; intro J1.
          - apply AxiomII'.
            apply f_x in J1; try apply H4.
            rewrite <- J1. rewrite Lemma4'.
            apply H8.
          - apply -> AxiomII' in J1.
            lazy beta in J1. rewrite Lemma4' in J1.
            rewrite <- H8 in J1.
            rewrite J1. apply x_fx; auto.
            apply AxiomII. rewrite H3.
            exists (f[x] - Σ {` λ k0 v, v =
              (dN f k0) [x0] / INR (k0 !) *
              (x - x0) ^^ k0 `} (S n)).
            apply AxiomII'. reflexivity. }
        rewrite I7. clear I7.
        assert (I7 : [x0, 0] ∈ dN {` λ x y, y =
          (dN f (S n)) [x0] / INR ((S n) !)
          * (x - x0) ^^ S n`} k).
        { rewrite Lemma5_7;
          try apply le_S; auto.
          apply AxiomII'.
          assert (I7 : x0 - x0 = 0). lra.
          rewrite I7. clear I7.
          assert (I8 : ∀ m, (0 < m)%nat -> 0^^m = 0).
          { intros m. induction m as [|m IHm].
            - intros J1. apply Nat.lt_irrefl in J1.
              contradiction.
            - intros J1. apply lt_n_Sm_le in J1 as J2.
              apply le_lt_or_eq in J2 as [J2 | J2].
              + apply IHm in J2. simpl. field.
              + rewrite <- J2. simpl. field. }
          assert (I9 : (0 < S n - k)%nat).
          { apply ArithProp.lt_minus_O_lt.
            apply le_lt_n_Sm. assumption. }
          rewrite I8; auto. field. apply not_0_INR.
          apply not_eq_sym. apply lt_0_neq.
          apply Lemma6_3_1. }
        assert (I8 : 0 = 0 - 0). lra.
        rewrite I8. apply Lemma5_18; auto.
        apply Lemma3'.
      + rewrite I1. apply H14.
        apply le_n. }
  assert (H16 : ∀ k, (S k - k = 1)%nat).
  { intros k. rewrite Nat.sub_succ_l.
    - rewrite Nat.sub_diag.
      reflexivity.
    - apply le_n. }
  assert (H17 : ∀ x k, (0 < k)%nat ->
    [x, (dN f (k-1))[x0] + (dN f k)[x0] * (x-x0)]
      ∈ (dN {` λ x y,
      y = Σ {` λ k1 v, v = (dN f k1)[x0] /
      (INR (k1!)) * (x - x0)^^k1 `} k `} (k-1))).
  { intros x k I1. destruct k as [|k].
    - apply Nat.lt_irrefl in I1.
      contradiction.
    - simpl minus. rewrite Nat.sub_0_r.
      assert (I2 : {` λ x y,
        y = Σ {` λ k1 v, v = (dN f k1)[x0] /
        (INR (k1!)) * (x - x0)^^k1 `} (S k) `} =
        {` λ x y, y = {` λ x1 y1,
        y1 = Σ {` λ k1 v, v = (dN f k1)[x0] /
        (INR (k1!)) * (x1 - x0)^^k1 `} k `}[x]
        + {` λ x1 y1, y1 = (dN f (S k))[x0] /
        (INR ((S k)!)) * (x1 - x0)^^(S k) `}[x] `}).
      { apply AxiomI; intros [x1 y1];
        split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H7 in J1. rewrite H11.
          rewrite Lemma4'. assumption.
        - apply -> AxiomII' in J1.
          lazy beta in J1. apply AxiomII'.
          simpl. rewrite H7.
          rewrite H11 in J1.
          rewrite Lemma4' in J1.
          assumption. }
      rewrite I2. clear I2.
      generalize (H13 x k); intros I2.
      assert (I3 : [x, (dN f (S k))[x0] * (x - x0)]
        ∈ dN {` λ x y, y = (dN f (S k))[x0] /
        (INR ((S k)!)) * (x - x0)^^(S k) `} k).
      { rewrite Lemma5_7;
        try apply (Nat.le_succ_diag_r k).
        apply AxiomII'.
        rewrite H16. rewrite <- Lemma6_3_3.
        simpl pow. field. apply not_0_INR.
        apply not_eq_sym.
        apply lt_0_neq. apply Lemma6_3_1. }
      apply Lemma5_18'; auto. apply Lemma3'. }
  assert (H18 : ∃ δ, 0 < δ /\ (∀ x, x ∈ Neighbor x0 δ
    -> (dN (Rn n) (n-1))[x] = (dN f (n-1))[x] -
    (dN f (n-1))[x0] - (dN f n)[x0] * (x - x0))).
  { generalize (Lemma5_6' f x0 n H2).
    intros [δ [I1 I2]].
    exists δ. split; [apply I1 | intros x I3].
    destruct n as [|n].
    - apply Nat.lt_irrefl in H0.
      contradiction.
    - simpl minus. rewrite Nat.sub_0_r.
      assert (I4 : [x, (dN f n)[x]] ∈
        dN f n).
      { apply x_fx.
        - apply Lemma5_16. assumption.
        - apply I2; auto. }
      generalize (H17 x (S n) H0).
      intros I5. simpl minus in I5.
      rewrite Nat.sub_0_r in I5.
      assert (I6 : Rn (S n) = {` λ x y,
        y = f[x] - {` λ x1 y1, y1 = Σ {` λ k v,
        v = (dN f k) [x0] / INR (k !) *
        (x1 - x0) ^^ k `} (S n) `}[x] `}).
      { rewrite H3. apply AxiomI;
        intros [x1 y1]; split; intro J1.
        - applyAxiomII' J1; apply AxiomII'.
          rewrite H11. assumption.
        - apply -> AxiomII' in J1;
          lazy beta in J1.
          apply AxiomII'. rewrite H11 in J1.
          assumption. }
      apply f_x.
      + apply Lemma5_16. apply H4.
      + assert (J1 : (dN f n)[x] - (dN f n)[x0]
          - (dN f (S n))[x0] * (x - x0) =
          (dN f n)[x] - ((dN f n)[x0]
          + (dN f (S n))[x0] * (x - x0))).
        field. rewrite J1. rewrite I6.
        apply Lemma5_18; auto. }
  destruct H18 as [δ1 [H18 H19]].
  assert (H20 : ∀ k, (k < n-1)%nat ->
    limit (dN (Rn n) k) x0 0 /\
    limit (dN {` λ x y, y = (x - x0)^^n `} k) x0 0).
  { intros k I1.
    assert (I2 : (S k <= n)%nat).
    { destruct n as [|n].
      - simpl in I1. apply Nat.nlt_0_r in I1.
        contradiction.
      - simpl in I1. rewrite Nat.sub_0_r in I1.
        apply Peano.le_n_S.
        apply Nat.lt_le_incl.
        assumption. }
    apply le_Sn_le in I2 as I3.
    split.
    - apply H15 in I2 as I4.
      simpl in I4. applyAxiomII' I4.
      assert (I5 : derivable (dN (Rn n) k) x0).
      { exists 0. assumption. }
      apply Theorem5_1 in I5 as [I6 I7].
      apply H15 in I3 as I8.
      apply f_x in I8.
      + rewrite I8 in I7. assumption.
      + apply Lemma5_16. auto.
    - rewrite Lemma5_7_1; auto.
      generalize (Lemma7' x0 (INR (mult_NM n k))
        x0 (n - k)).
      intros I4.
      assert (I5 : (INR (mult_NM n k) *
        (x0 - x0) ^^ (n - k)) = 0).
      { assert (J1 : x0 - x0 = 0). lra.
        rewrite J1. assert (J2 : (0 < n - k)%nat).
        { apply ArithProp.lt_minus_O_lt.
          apply le_S_gt. assumption. }
        rewrite Lemma6_3_4; auto.
        field. }
      rewrite I5 in I4.
      assumption. }
  assert (H21 : ∀ k, (0 < k <= n-1)%nat ->
    (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂
    dom[dN (Rn n) k] /\ Neighbor0 x0 δ' ⊂
    dom[dN {` λ x y, y = (x - x0)^^n `} k] /\
    (∀ x, x ∈ Neighbor0 x0 δ' ->
    (dN {` λ x y, y = (x - x0)^^n `} k)[x] <> 0))).
  { intros k I1. assert (I2 : (k < n)%nat).
    { destruct n as [|n].
      - apply Nat.lt_irrefl in H0.
        contradiction.
      - simpl in I1. rewrite Nat.sub_0_r in I1.
        apply le_lt_n_Sm. apply I1. }
    generalize (Lemma5_6 (Rn n) x0 n (H9 n) k I2).
    intros [δ [I3 I4]]. exists δ.
    apply Nat.lt_le_incl in I2 as I5.
    repeat split; auto.
    - intros x J1. apply I4.
      applyAxiomII J1. apply AxiomII.
      apply J1.
    - rewrite Lemma5_7_1; auto.
      intros x J1. apply AxiomII.
      exists (INR (mult_NM n k) *
        (x - x0) ^^ (n - k)).
      apply AxiomII'. reflexivity.
    - intros x J1. rewrite Lemma5_7_1; auto.
      rewrite Lemma4'.
      apply Rmult_integral_contrapositive_currified.
      + apply not_0_INR. apply mult_NM_ne_0.
      + apply Lemma6_3_5. applyAxiomII J1.
        apply Lemma2 in J1. apply J1. }
  assert (H22 : limit {` λ x y, y = (dN (Rn n) (n-1))[x]
    / (dN {` λ x y, y = (x - x0)^^n `} (n-1))[x] `} x0 0).
  { assert (I1 : (n - 1 <= n)%nat).
    { destruct n as [|n].
      - simpl. apply le_n.
      - simpl. rewrite Nat.sub_0_r.
        apply Nat.le_succ_diag_r. }
    rewrite Lemma5_7_1; auto.
    assert (I2 : {` λ x y, y = (dN (Rn n) (n - 1)) [x]
      / {` λ x1 y0, y0 = INR (mult_NM n (n - 1)) *
      (x1 - x0) ^^ (n - (n - 1))`} [x] `} =
      {` λ x y, y = (dN (Rn n) (n - 1)) [x] /
        (INR (n!) * (x - x0)) `}).
    { assert (K1 :(n - (n - 1) = 1)%nat /\
          (mult_NM n (n - 1) = n!)%nat).
      { destruct n as [|n].
        - apply Nat.lt_irrefl in H0.
          contradiction.
        - assert (L1 : (S n - 1 = n)%nat).
          { simpl. apply Nat.sub_0_r. }
          split.
          + rewrite L1. apply H16.
          + rewrite L1. rewrite Lemma6_3_3.
            reflexivity. }
      destruct K1 as [K1 K2].
      apply AxiomI; intros [x y];
      split; intro J1;
      applyAxiomII' J1; apply AxiomII'.
      - rewrite Lemma4' in J1.
        rewrite K1 in J1.
        rewrite K2 in J1.
        simpl in J1.
        assert (K3 : (x - x0) * 1 = x - x0).
        field. rewrite K3 in J1.
        assumption.
      - rewrite K1; rewrite K2.
        rewrite Lemma4'. simpl.
        assert (K3 : (x - x0) * 1 = x - x0).
        field. rewrite K3.
        assumption. }
    rewrite I2. clear I2.
    assert (I2 : Function {` λ x y, y =
      (dN (Rn n) (n - 1)) [x] /
      (INR (n!) * (x - x0)) `}).
    { intros x y z J1 J2.
      applyAxiomII' J1; applyAxiomII' J2.
      rewrite J2; assumption. }
    split; auto.
    assert (I3 : (n = S (n - 1))%nat).
    { destruct n as [|n].
      - apply Nat.lt_irrefl in H0.
        contradiction.
      - assert (J1 : (S n - 1 = n)%nat).
        { simpl. apply Nat.sub_0_r. }
        rewrite J1. reflexivity. }
    assert (I4 : Function (dN f n)).
    { apply Lemma5_16; assumption. }
    apply x_fx in H2; auto.
    pattern n at 2 in H2.
    rewrite I3 in H2. simpl dN in H2.
    apply -> AxiomII' in H2.
    lazy beta in H2. unfold derivative in H2.
    destruct H2 as [I5 [[δ1' [I6 I7]] I8]].
    unfold limit in I8.
    destruct I8 as [I8 [δ' [I9 [I10 I11]]]].
    exists δ'. split; [assumption | split].
    - intros x J1. apply AxiomII.
      exists ((dN (Rn n) (n - 1)) [x] /
        (INR (n !) * (x - x0))).
      apply AxiomII'. reflexivity.
    - intros ε J1. generalize (I11 ε J1).
      intros [δ2 [[J2 J3] J4]].
      generalize (Lemma1 δ1 δ2 H18 J2).
      intros [δ [J5 [J6 J7]]].
      exists δ. split; [lra | intros x J8].
      assert (J9 :∀ x, {` λ x1 y, y =
        (dN (Rn n) (n - 1)) [x1] /
        (INR (n !) * (x1 - x0))`} [x] =
        (dN (Rn n) (n - 1)) [x] /
        (INR (n !) * (x - x0))).
      { intros t. apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite J9.
      assert (J10 : x ∈ Neighbor x0 δ1).
      { apply AxiomII. lra. }
      assert (J11 : 0 < Abs [x - x0] < δ2). lra.
      generalize (H19 x J10).
      intros J12. rewrite J12.
      generalize (J4 x J11).
      intros J13.
      assert (J14 : {` λ x y, y =
        ((dN f (n - 1)) [x] - (dN f (n - 1)) [x0])
        / (x - x0) `} [x] =
        ((dN f (n - 1)) [x] - (dN f (n - 1)) [x0])
        / (x - x0)).
      { apply f_x.
        - intros x1 y1 z1 K1 K2.
          applyAxiomII' K1; applyAxiomII' K2.
          rewrite K2; assumption.
        - apply AxiomII'. reflexivity. }
      rewrite J14 in J13. clear J14.
      assert (J14 : ∀ k,  1 <= INR (k!)).
      { intros k. assert (K1 : 1 = INR 1%nat).
        { simpl. reflexivity. }
        rewrite K1. apply le_INR.
        induction k as [|k IHk].
        - simpl. apply le_n.
        - simpl. apply le_plus_trans.
          assumption. }
      assert (J15 : 0 < INR (n !)).
      { apply lt_0_INR. apply Lemma6_3_1. }
      assert (J16 : INR (n !) <> 0).
      { apply not_eq_sym.
        apply Rlt_not_eq. auto. }
      assert (J17 : ((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0] - (dN f n) [x0]
        * (x - x0)) / (INR (n !) * (x - x0))
        - 0 = (((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0)
        - (dN f n) [x0]) / (INR (n !))).
      { field. split; auto.
        - apply Lemma2 in J8. apply J8. }
      rewrite J17. clear J17.
      rewrite Abs_div; auto.
      rewrite (Abs_gt (INR (n!))); auto.
      apply Rmult_lt_reg_r with (r := INR (n !)); auto.
      assert (J17 : Abs [((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0) -
        (dN f n) [x0]] / INR (n !) * INR (n !) =
        Abs [((dN f (n - 1)) [x] -
        (dN f (n - 1)) [x0]) / (x - x0) -
        (dN f n) [x0]]).
      { field. assumption. }
      rewrite J17. clear J17.
      assert (J17 : ε <= ε * INR (n !)).
      { pattern ε at 1. rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; auto. lra. }
      lra. }
  generalize (Lemma6_1 (Rn n) {` λ x y,
    y = (x - x0)^^n `} x0 0 (n-1) H20 H21 H22).
  intros H23. split.
  - unfold InfinitesimalHigherOrder.
    split; [auto | split];
    [apply Lemma3 | split]; auto.
    exists 1. split; [lra | repeat split].
    + intros x I1. rewrite H3. apply AxiomII.
      exists (f[x] - Σ {` λ k v, v =
        (dN f k)[x0] / INR (k !)
        * (x - x0) ^^ k`} n).
      apply AxiomII'. reflexivity.
    + intros x I1. apply AxiomII.
      exists ((x - x0) ^^ n).
      apply AxiomII'. reflexivity.
    + intros x I1. rewrite Lemma4.
      apply Lemma6_3_5. applyAxiomII I1.
      apply Lemma2 in I1.
      apply I1.
  - intros x. rewrite H5.
    field.
Qed.

End A6_3.

Export A6_3.