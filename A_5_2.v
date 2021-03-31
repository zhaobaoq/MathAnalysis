Require Export A_5_1.

Module A5_2.

(* 5.2 求导法则 *)

Fixpoint pow (r:R) (n:nat) : R :=
  match n with
    | O => 1
    | S n => Rmult r (pow r n)
  end.
Notation "r ^^ n" :=(pow r n) (at level 20).

Lemma Lemma1 : ∀ a b, a > 0 -> b > 0 -> 
   ∃ c, c > 0 /\ c < a /\ c < b.
Proof.
  intros a b H0 H1.
  destruct (Rlt_or_le a b) as [H2 | H2].
  - exists (a/2). repeat split; lra.
  - exists (b/2). repeat split; lra.
Qed.

Lemma Lemma1' : ∀ a b c, a > 0 -> b > 0 -> c > 0 -> 
   ∃ d, d > 0 /\ d < a /\ d < b /\ d < c.
Proof.
  intros a b c H0 H1 H2.
  destruct (Rlt_or_le a b) as [H3 | H3].
  - destruct (Rlt_or_le a c) as [H4 | H4].
    + exists (a/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
  - destruct (Rlt_or_le b c) as [H4 | H4].
    + exists (b/2). repeat split; lra.
    + exists (c/2). repeat split; lra.
Qed.

Lemma Lemma2 : ∀ a b, 0 < Abs[a] < b ->
  a <> 0 /\ -b < a < b.
Proof.
  intros a b [H0 H1].
  apply Abs_not_eq_0 in H0.
  apply Abs_R in H1. split; assumption.
Qed.

Theorem Theorem5_4_1 : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative {` λ x y, y = u[x] + v[x] `}
    x0 (u '[x0] + v '[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1].
  apply derEqual in H0 as H2.
  apply derEqual in H1 as H3.
  rewrite H2; rewrite H3.
  clear H2 H3.
  assert (H3 : Function {` λ x y, y = u[x] + v[x] `}).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H0 as [H0 [[δ1' [H4 H5]] H6]].
  destruct H1 as [H1 [[δ2' [H7 H8]] H9]].
  generalize (Lemma1 δ1' δ2' H4 H7);
  intros [δ' [H10 [H11 H12]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] + v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H13 : Function {` λ x y, y =
      ({` λ x y, y = u[x] + v[x] `}[x]
      - {` λ x y, y = u[x] + v[x] `}[x0])
      / (x - x0) `}).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists (({` λ x y, y = u[x] + v[x] `}[x]
      - {` λ x y, y = u[x] + v[x] `}[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H14.
      destruct H6 as [H6 [δ3' [H15 [H16 H17]]]].
      destruct H9 as [H9 [δ4' [H18 [H19 H20]]]].
      assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22.
      destruct H22 as [δ2 [[H22 H26] H23]].
      apply H17 in H21 as [δ1 [[H24 H27] H25]].
      generalize (Lemma1' δ' δ1 δ2 H10 H24 H22).
      intros [δ [H28 [H29 [H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : {` λ x y, y =
        ({` λ x y, y = u[x] + v[x] `}[x]
        - {` λ x y, y = u[x] + v[x] `}[x0])
        / (x - x0) `}[x] =
        ({` λ x y, y = u[x] + v[x] `}[x]
        - {` λ x y, y = u[x] + v[x] `}[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, {` λ x y,
        y = u[x] + v[x] `} [x1] = u[x1] + v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H33; auto.
      rewrite H33; auto.
      assert (H38 : 0 < Abs [x - x0] < δ1). lra.
      apply H25 in H38.
      assert (H39 : 0 < Abs [x - x0] < δ2). lra.
      apply H23 in H39.
      assert (H40 : {` λ x y, y =
        (u[x] - u[x0]) / (x - x0) `} [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : {` λ x y, y =
        (v[x] - v[x0]) / (x - x0) `} [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] + v[x] -
        (u[x0] + v[x0])) / (x - x0)
        - (y1 + y2) = ((u[x] - u[x0]) / (x - x0) - y1)
        + ((v[x] - v[x0]) / (x - x0) - y2)).
      { field. apply Lemma2 in H32.
        apply H32. }
      rewrite H40.
      generalize (Abs_plus_le ((u[x] - u[x0])
        / (x - x0) - y1) ((v[x] - v[x0])
        / (x - x0) - y2)). intro H41. lra.
Qed.

Theorem Theorem5_4_2 : ∀ (u v : Fun) (x0 : R),
  derivable u x0 -> derivable v x0 ->
  derivative {` λ x y, y = u[x] - v[x] `}
    x0 (u '[x0] - v '[x0]).
Proof.
  intros u v x0 [y1 H0] [y2 H1].
  apply derEqual in H0 as H2.
  apply derEqual in H1 as H3.
  rewrite H2; rewrite H3.
  clear H2 H3.
  assert (H3 : Function {` λ x y, y = u[x] - v[x] `}).
  { intros x y z I1 I2. applyAxiomII' I1;
    applyAxiomII' I2.
    rewrite I2; apply I1. }
  split; auto. destruct H0 as [H0 [[δ1' [H4 H5]] H6]].
  destruct H1 as [H1 [[δ2' [H7 H8]] H9]].
  generalize (Lemma1 δ1' δ2' H4 H7);
  intros [δ' [H10 [H11 H12]]]. split.
  - exists δ'.
    split; auto. intros x I1.
    applyAxiomII I1. apply AxiomII.
    exists (u[x] - v[x]). apply AxiomII'.
    repeat split; auto.
  - assert (H13 : Function {` λ x y, y =
      ({` λ x y, y = u[x] - v[x] `}[x]
      - {` λ x y, y = u[x] - v[x] `}[x0])
      / (x - x0) `}).
    { intros x y z I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; apply I1. }
    split; auto. exists δ'. split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists (({` λ x y, y = u[x] - v[x] `}[x]
      - {` λ x y, y = u[x] - v[x] `}[x0])
      / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H14.
      destruct H6 as [H6 [δ3' [H15 [H16 H17]]]].
      destruct H9 as [H9 [δ4' [H18 [H19 H20]]]].
      assert (H21 : ε/2 > 0). lra.
      apply H20 in H21 as H22.
      destruct H22 as [δ2 [[H22 H26] H23]].
      apply H17 in H21 as [δ1 [[H24 H27] H25]].
      generalize (Lemma1' δ' δ1 δ2 H10 H24 H22).
      intros [δ [H28 [H29 [H30 H31]]]].
      exists δ. split; try lra. intros x H32.
      assert (H33 : {` λ x y, y =
        ({` λ x y, y = u[x] - v[x] `}[x]
        - {` λ x y, y = u[x] - v[x] `}[x0])
        / (x - x0) `}[x] =
        ({` λ x y, y = u[x] - v[x] `}[x]
        - {` λ x y, y = u[x] - v[x] `}[x0])
        / (x - x0)).
      { apply f_x; auto.
        apply AxiomII'. reflexivity. }
      rewrite H33. clear H33.
      assert (H33 : ∀ x1, {` λ x y,
        y = u[x] - v[x] `} [x1] = u[x1] - v[x1]).
      { intros x1. apply f_x; auto.
        apply AxiomII'. repeat split; auto. }
      rewrite H33; auto.
      rewrite H33; auto.
      assert (H38 : 0 < Abs [x - x0] < δ1). lra.
      apply H25 in H38.
      assert (H39 : 0 < Abs [x - x0] < δ2). lra.
      apply H23 in H39.
      assert (H40 : {` λ x y, y =
        (u[x] - u[x0]) / (x - x0) `} [x]
        = (u[x] - u[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H38. clear H40.
      assert (H40 : {` λ x y, y =
        (v[x] - v[x0]) / (x - x0) `} [x]
        = (v[x] - v[x0]) / (x - x0)).
      { apply f_x; auto. apply AxiomII'. reflexivity. }
      rewrite H40 in H39. clear H40.
      assert (H40 : (u[x] - v[x] -
        (u[x0] - v[x0])) / (x - x0)
        - (y1 - y2) = ((u[x] - u[x0]) / (x - x0) - y1)
        - ((v[x] - v[x0]) / (x - x0) - y2)).
      { field. apply Lemma2 in H32.
        apply H32. }
      rewrite H40.
      generalize (Abs_minus_le ((u[x] - u[x0])
        / (x - x0) - y1) ((v[x] - v[x0])
        / (x - x0) - y2)). intro H41. lra.
Qed.

Lemma Lemma5_1 : ∀ (u : Fun) (c : R),
  Function {` λ x y, y = c * u[x] `}.
Proof.
  intros u c x y z I1 I2. applyAxiomII' I1;
  applyAxiomII' I2. rewrite I2; assumption.
Qed.

Lemma Lemma5_2 : ∀ (u : Fun) (c x0 : R),
  {` λ x y, y = c * u[x] `}[x0] = c * u[x0].
Proof.
  intros u c x0. apply f_x; try apply Lemma5_1.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma5_3 : ∀ (u : Fun) (c x0 : R),
  derivable u x0 -> derivative {` λ x y, y = c * u[x] `}
    x0 (c * u '[x0]).
Proof.
  intros u c x0 [y H0]. apply derEqual in H0 as H1.
  rewrite H1. clear H1.
  split; try apply Lemma5_1. unfold derivative in H0.
  destruct H0 as [H0 [[δ' [H1 H2]] H3]]. split.
  - exists δ'. split; auto. intros x I1.
    apply AxiomII. exists (c*u[x]).
    apply AxiomII'. reflexivity.
  - assert (H4 : Function {` λ x y0, y0 =
            ({` λ x1 y1, y1 = c * u[x1] `}[x] -
             {` λ x1 y1, y1 = c * u[x1] `} [x0])
             / (x - x0) `} ).
    { intros x1 y1 z1 I1 I2. applyAxiomII' I1;
      applyAxiomII' I2. rewrite I2; assumption. }
    split; auto. exists δ'.
    split; [assumption | split].
    + intros x I1. apply AxiomII.
      exists (({` λ x1 y1, y1 = c * u[x1] `}[x] -
             {` λ x1 y1, y1 = c * u[x1] `} [x0])
             / (x - x0)).
      apply AxiomII'. reflexivity.
    + intros ε H5. unfold limit in H3.
      destruct H3 as [H3 [δ1' [H6 [H7 H8]]]].
      assert (H16 : ∀ x, {` λ x y0, y0 =
        ({` λ x1 y1, y1 = c * u[x1] `}[x] -
         {` λ x1 y1, y1 = c * u[x1] `} [x0])
         / (x - x0) `}[x] =
         ({` λ x1 y1, y1 = c * u[x1] `}[x] -
         {` λ x1 y1, y1 = c * u[x1] `} [x0])
         / (x - x0)).
      { intros x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      destruct classic with (P := c = 0) as [J0 | J0].
      * exists (δ'/2). split; [lra | intros x H9].
        rewrite H16. rewrite Lemma5_2. rewrite Lemma5_2.
        rewrite J0 in *.
        apply Lemma2 in H9. apply Abs_R.
        assert (I1 : (0 * u [x] - 0 * u [x0])
          / (x - x0) - 0 * y = 0).
        { field. apply H9. }
        rewrite I1. lra.
      * assert (J1 : Abs[c] > 0).
        { apply Abs_not_eq_0. assumption. }
        assert (J2 : ε/Abs[c] > 0).
        { apply Rdiv_lt_0_compat; assumption. }
        apply H8 in J2 as H9.
        destruct H9 as [δ1 [[H9 H10] H11]].
        generalize (Lemma1 δ' δ1 H1 H9).
        intros [δ [H12 [H13 H14]]].
        exists δ. split; [lra | intros x H15].
        rewrite H16. clear H16.
        rewrite Lemma5_2. rewrite Lemma5_2.
        assert (H16 : 0 < Abs [x - x0] < δ1). lra.
        apply H11 in H16.
        assert (H17 : {` λ x y, y = (u[x] - u[x0])
          / (x - x0) `} [x] = (u[x] - u[x0])
          / (x - x0)).
        { apply f_x; auto. apply AxiomII'.
          reflexivity. }
        rewrite H17 in H16.
        apply Lemma2 in H15.
        assert (H18 : (c * u[x] - c * u[x0]) / (x - x0)
          - c * y = c * ((u [x] - u [x0]) / (x - x0) - y)).
        { field. apply H15. }
        rewrite H18. rewrite Abs_mult.
        apply Rmult_lt_compat_l with (r := Abs[c]) in H16;
        auto. assert (H19 : Abs [c] * (ε / Abs [c]) = ε).
        { field. lra. }
        rewrite H19 in H16. assumption.
Qed.

Lemma Lemma3 : ∀ a n, Function {` λ x y,
  y = (x - a)^^n `}.
Proof.
  intros a n x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma3' : ∀ a c n, Function {` λ x y,
  y = c * (x - a)^^n `}.
Proof.
  intros a c n x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma4 : ∀ a x n, {` λ x y,
  y = (x - a)^^n `} [x] = (x - a)^^n.
Proof.
  intros a x n. apply f_x; try apply Lemma3.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma4' : ∀ a c x n, {` λ x y,
  y = c * (x - a)^^n `} [x] = c * (x - a)^^n.
Proof.
  intros a c x n. apply f_x; try apply Lemma3'.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma5 : ∀ a, Function {` λ x y : R, y = x - a `}.
Proof.
  intros a x1 y1 z1 I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2. assumption.
Qed.

Lemma Lemma6 : ∀ a x, {` λ x y, y = x - a `} [x] = x - a.
Proof.
  intros a x. apply f_x; try apply Lemma5.
  apply AxiomII'. reflexivity.
Qed.

(* 幂函数连续 *)
Lemma Lemma7 : ∀ a x0 n, limit
  {` λ x y, y = (x - a)^^n `} x0 ((x0 - a)^^n).
Proof.
  intros a x0 n. generalize dependent x0.
  induction n as [|n IHn].
  - intro x0. split; try apply Lemma3. exists 2.
    split; try lra. split.
    + intros x H0. simpl. apply AxiomII. exists 1.
      apply AxiomII'. reflexivity.
    + intros ε H0. exists 1. split; try lra.
      intros x H1. rewrite Lemma4.
      simpl. apply Abs_R. lra.
  - intros x0. simpl.
    assert (H0 : {` λ x y, y = (x - a) * (x - a)^^n `} =
      {` λ x y, y = x - a `} **
      {` λ x y, y = (x - a)^^n `}).
    { apply AxiomI. intros [x y]. split; intros I1;
      applyAxiomII' I1; apply AxiomII'.
      - repeat split.
        + apply AxiomII. exists (x - a).
          apply AxiomII'. reflexivity.
        + apply AxiomII. exists ((x - a)^^n).
          apply AxiomII'. reflexivity.
        + rewrite Lemma6. rewrite Lemma4.
          assumption.
      - destruct I1 as [I1 [I2 I3]].
        rewrite I3. rewrite Lemma6. rewrite Lemma4.
        reflexivity. }
    rewrite H0. apply Theorem3_7_3; auto.
    split; try apply Lemma5. exists 1.
    split; [lra | split].
    + intros x I1. apply AxiomII.
      exists (x - a). apply AxiomII'. reflexivity.
    + intros ε I1. assert (I2 : 1 > 0). lra.
      generalize (Lemma1 ε 1 I1 I2).
      intros [δ [I3 [I4 I5]]]. exists δ.
      split; [lra | intros x I6].
      rewrite Lemma6.
      assert (I7 : x - a - (x0 - a) = x - x0).
      field. rewrite I7. lra.
Qed.

(* 幂函数导数 *)
Lemma Lemma5_4 : ∀ a x0 n, derivative
  {` λ x y, y = (x - a)^^n `} x0
  (INR n * ((x0 - a) ^^ (n - 1))).
Proof.
  intros a x0 n.
  split; try apply Lemma3. split.
  - exists 1. split; try lra.
    intros x I1. apply AxiomII.
    exists ((x - a)^^n). apply AxiomII'.
    reflexivity.
  - rewrite Lemma4.
    assert (H1 : {` λ x y,
      y = ({` λ x1 y0, y0 = (x1 - a) ^^ n `} [x]
      - (x0 - a) ^^ n) / (x - x0) `}
      = {` λ x y, y = ((x - a) ^^ n
        - (x0 - a) ^^ n) / (x - x0) `}).
    { apply AxiomI. intros [x y].
      split; intros I1; apply AxiomII'; applyAxiomII' I1.
      - rewrite Lemma4 in I1. assumption.
      - rewrite Lemma4. assumption. }
    rewrite H1. clear H1.
    assert (H0 : ∀ x0 n, Function
      {` λ x y, y = ((x - a)^^n
        - (x0 - a)^^n) / (x - x0) `}).
    { intros x1 n0. intros x2 y2 z2 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2. assumption. }
    induction n as [|n IHn].
    + split; auto. exists 1. split; try lra; split.
      * intros x I1. simpl. apply AxiomII.
        exists ((1 - 1) / (x - x0)).
        apply AxiomII'. reflexivity.
      * intros ε I1. exists (1/2).
        split; try lra. intros x [I2 I3].
        apply Abs_not_eq_0 in I2.
        assert (I4 : {` λ x1 y,
          y = ((x1 - a)^^0 - (x0 - a)^^0)
            / (x1 - x0) `} [x] = 0).
        { apply f_x; auto. apply AxiomII'.
          simpl. field. assumption. }
        rewrite I4. simpl. apply Abs_R. lra.
    + assert (H1 : ∀ x, ((x - a)^^S n -
        (x0 - a)^^S n) / (x - x0)
        = (x - a)^^n * (x - x0) / (x - x0)
          + (x0 - a) * ((x - a)^^n -
          (x0 - a)^^n) / (x - x0)).
      { intros x. simpl.
        assert (I1 : (x - a) * (x - a)^^n
          - (x0 - a) * (x0 - a)^^n
          = (x - a)^^n * (x - x0) +
          (x0 - a) * ((x - a)^^n - (x0 - a)^^n)).
        field. rewrite I1. rewrite Rdiv_plus_distr.
        reflexivity. }
      assert (H2 : (INR (S n) * (x0 - a)^^(S n - 1))
        = (x0 - a)^^n + INR n * (x0 - a)^^n).
      { rewrite S_INR.
        assert (I1 : (S n - 1 = n)%nat).
        { simpl. rewrite minus_n_O.
          reflexivity. }
        rewrite I1. field. }
      rewrite H2. clear H2.
      assert (H2 : Function {` λ x y, y =
        (x - a) ^^ n * (x - x0) / (x - x0) `}).
      { intros x y z I1 I2. applyAxiomII' I1;
        applyAxiomII' I2. rewrite I2; assumption. }
      assert (H3 : Function {` λ x y, y =
          (x0 - a) * ((x - a)^^n
            - (x0 - a)^^n) / (x - x0) `}).
      { intros x y z I1 I2. applyAxiomII' I1;
        applyAxiomII' I2. rewrite I2; assumption. }
      assert (H4: ∀ x, {` λ x1 y0,
        y0 = (x1 - a)^^n * (x1 - x0)
         / (x1 - x0) `} [x]
        = (x - a)^^n * (x - x0) / (x - x0)).
      { intro x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      assert (H5 : ∀ x, {` λ x1 y0,
        y0 = (x0 - a) * ((x1 - a)^^n - (x0 - a)^^n)
        / (x1 - x0) `} [x] = (x0 - a) *
          ((x - a)^^n - (x0 - a)^^n) / (x - x0)).
      { intro x. apply f_x; auto. apply AxiomII'.
        reflexivity. }
      assert (H6 : {` λ x y, y =
        ((x - a)^^S n - (x0 - a)^^S n) / (x - x0) `}
        = {` λ x y, y = (x - a) ^^ n * (x - x0)
          / (x - x0) `} \+ {` λ x y, y =
          (x0 - a) * ((x - a)^^n -
          (x0 - a)^^n) / (x - x0) `}).
      { apply AxiomI. intros [x y]; split; intro I1;
        applyAxiomII' I1; apply AxiomII'.
        - repeat split.
          + apply AxiomII.
            exists ((x - a)^^n * (x - x0) / (x - x0)).
            apply AxiomII'. reflexivity.
          + apply AxiomII.
            exists ((x0 - a) * ((x - a)^^n
              - (x0 - a)^^n) / (x - x0)).
            apply AxiomII'. reflexivity.
          + rewrite H4; rewrite H5.
            rewrite I1. apply H1.
        - destruct I1 as [I1 [I4 I5]].
          rewrite H4 in I5.
          rewrite H5 in I5.
          rewrite I5. symmetry.
          apply H1. }
      rewrite H6. clear H6.
      apply Theorem3_7_1.
      * generalize (Lemma7 a x0 n). unfold limit.
        intros [I2 [δ' [I3 [I4 I5]]]].
        split; auto. exists δ'.
        split; [assumption | split].
        -- intros x I1. apply AxiomII.
          exists ((x - a)^^n * (x - x0) / (x - x0)).
          apply AxiomII'. reflexivity.
        -- intros ε I1. apply I5 in I1 as I6.
          destruct I6 as [δ [I6 I7]].
          exists δ; split; [assumption | intros x I8].
          apply I7 in I8 as I9.
          rewrite Lemma4 in I9.
          apply Lemma2 in I8 as [I8 I10].
          rewrite H4.
          assert (I11 : (x - a)^^n * (x - x0) / (x - x0)
            = (x - a)^^n). field; auto.
          rewrite I11. assumption.
      * assert (I1 : INR n * (x0 - a) ^^ n =
          (x0 - a) * (INR n * (x0 - a) ^^ (n - 1))).
        { destruct n.
          - simpl. field.
          - rewrite <- Rmult_assoc.
            rewrite (Rmult_comm (x0 - a) (INR (S n))).
            rewrite Rmult_assoc.
            simpl. rewrite <- minus_n_O.
            reflexivity. }
        rewrite I1. clear I1.
        assert (I1 : Function {` λ x y : R,
          y = x0 - a `}).
        { intros x1 y1 z1 I1 I2.
          applyAxiomII' I1; applyAxiomII' I2.
          rewrite I2. assumption. }
        assert (I2 : ∀ x, {` λ x y : R,
          y = x0 - a `}[x] = x0 - a).
        { intros x. apply f_x; auto.
          apply AxiomII'. reflexivity. }
        assert (I3 : Function {` λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) `}).
        { intros x1 y1 z1 J1 J2.
          applyAxiomII' J1; applyAxiomII' J2.
          rewrite J2. assumption. }
        assert (I4 : ∀ x, {` λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) `}[x]
          = ((x - a)^^n - (x0 - a)^^n) / (x - x0)).
        { intros x. apply f_x; auto.
          apply AxiomII'. reflexivity. }
        assert (I5 : {` λ x y, y = (x0 - a) *
          ((x - a)^^n - (x0 - a)^^n) / (x - x0) `}
          = {` λ x y, y = x0 - a `} ** {` λ x y,
          y = ((x - a)^^n - (x0 - a)^^n) / (x - x0) `}).
        { apply AxiomI. intros [x y]; split; intro J1;
          applyAxiomII' J1; apply AxiomII'.
          - rewrite I4. rewrite I2.
            repeat split.
            + apply AxiomII. exists (x0 - a).
              apply AxiomII'. reflexivity.
            + apply AxiomII.
              exists (((x - a)^^n -
                (x0 - a)^^n) / (x - x0)).
              apply AxiomII'. reflexivity.
            + lra.
          - destruct J1 as [J1 [J2 J3]].
            rewrite I4 in J3. rewrite I2 in J3.
            lra. }
        rewrite I5. clear I5.
        apply Theorem3_7_3; auto.
        split; auto. exists 2. split; [lra | split].
        -- intros x J1. apply AxiomII.
          exists (x0 - a). apply AxiomII'.
          reflexivity.
        -- intros ε J1. exists 1.
          split; [lra | intros x J2].
          rewrite I2. apply Abs_R. lra.
Qed.

Lemma Lemma5_5 : ∀ a c x0 n, derivative {` λ x y,
  y = c * (x - a)^^n `} x0
  (c * INR n  * (x0 - a)^^(n - 1)).
Proof.
  intros a c x0 n.
  assert (H0 : ∃ u, u = {` λ x y, y = (x - a)^^n `}).
  { exists {` λ x y, y = (x - a)^^n `}.
    reflexivity. }
  destruct H0 as [u H0].
  assert (H1 : {` λ x y, y = c * (x - a)^^n `} =
    {` λ x y, y = c * u[x] `}).
  { rewrite H0. apply AxiomI. intros [x y]; split;
    intros I1; applyAxiomII' I1; apply AxiomII'.
    - rewrite Lemma4. assumption.
    - rewrite Lemma4 in I1. assumption. }
  rewrite H1.
  generalize (Lemma5_4 a x0 n). intro H2.
  rewrite <- H0 in H2.
  assert (H3 : c * INR n * (x0 - a)^^(n - 1) =
    c * u '[x0]).
  { apply derEqual in H2 as H3.
    rewrite H3. field. }
  rewrite H3. apply Lemma5_3.
  exists (INR n * (x0 - a) ^^ (n - 1)).
  assumption.
Qed.

Lemma Lemma5_9 : ∀ f g x0 y0, Function g ->
  (∃ δ, 0 < δ /\ (∀ x, x ∈ Neighbor x0 δ ->
    x ∈ dom[g] /\ f[x] = g[x]))
  -> derivative f x0 y0 -> derivative g x0 y0.
Proof.
  intros f g x0 y0 H0 [δ [H1 H2]] H3.
  split; [auto | split].
  - exists δ. split; auto.
    intros x I1. apply H2. assumption.
  - unfold limit. unfold derivative in H3.
    destruct H3 as [H3 [[δ' [I1 I2]] I3]].
    unfold limit in I3.
    destruct I3 as [I3 [δ1' [I4 [I5 I6]]]].
    split.
    + intros x y z J1 J2. applyAxiomII' J1;
      applyAxiomII' J2. rewrite J2; assumption.
    + exists δ1'. split; [auto | split].
      * intros x J1. apply AxiomII.
        exists ((g [x] - g [x0]) / (x - x0)).
        apply AxiomII'. reflexivity.
      * intros ε J1. apply I6 in J1 as J2.
        destruct J2 as [δ1 [[J2 J3] J4]].
        generalize (Lemma1 δ δ1 H1 J2).
        intros [δ2 [J5 [J6 J7]]].
        exists δ2. split; try lra.
        intros x J8.
        assert (J9 : 0 < Abs [x - x0] < δ1). lra.
        apply J4 in J9.
        assert (J10 : {` λ x y, y =
          (f [x] - f [x0]) / (x - x0) `} [x]
          = (f [x] - f [x0]) / (x - x0)).
        { apply f_x; auto. apply AxiomII'.
          reflexivity. }
        rewrite J10 in J9.
        clear J10.
        assert (J10 : {` λ x y, y =
          (g [x] - g [x0]) / (x - x0) `} [x]
          = (g [x] - g [x0]) / (x - x0)).
        { apply f_x.
          - intros x1 y1 z1 K1 K2.
            applyAxiomII' K1;
            applyAxiomII' K2.
            rewrite K2; assumption.
          - apply AxiomII'. reflexivity. }
        rewrite J10. assert (J11 : x ∈ Neighbor x0 δ).
        { apply AxiomII. lra. }
        apply H2 in J11 as [J11 J12].
        rewrite <- J12.
        assert (J13 : x0 ∈ Neighbor x0 δ).
        { apply AxiomII. apply Abs_R. lra. }
        apply H2 in J13 as [J14 J15].
        rewrite <- J15. assumption.
Qed.

(* 常数函数导数 *)
Lemma Lemma5_10 : ∀ c, Function {` λ x y : R, y = c `}.
Proof.
  intros c x y z I1 I2.
  applyAxiomII' I1; applyAxiomII' I2.
  rewrite I2; assumption.
Qed.

Lemma Lemma5_11 : ∀ c x, {` λ x y : R, y = c `}[x] = c.
Proof.
  intros c x. apply f_x;
  try apply Lemma5_10.
  apply AxiomII'. reflexivity.
Qed.

Lemma Lemma5_12 : ∀ c x0, derivative
  {` λ x y, y = c `} x0 0.
Proof.
  intros c x.
  split; [apply Lemma5_10 | split].
  - exists 1. split; [lra | intros x0 I1].
    apply AxiomII. exists c.
    apply AxiomII'. reflexivity.
  - unfold limit. split.
    + intros x1 y1 z1 I1 I2.
      applyAxiomII' I1; applyAxiomII' I2.
      rewrite I2; assumption.
    + exists 2. split; [lra | split].
      * intros x0 I1. apply AxiomII.
        exists (({` λ _ y1 : R, y1 = c `} [x0]
          - {` λ _ y1 : R, y1 = c `} [x]) /
          (x0 - x)).
        apply AxiomII'. reflexivity.
      * intros ε I1. exists 1.
        split; [lra | intros x0 I2].
        -- assert (I3 : {` λ x1 y, y =
           ({` λ _ y0 : R, y0 = c `} [x1]
           - {` λ _ y0 : R,y0 = c `} [x]) /
           (x1 - x) `} [x0] = 0).
          { apply f_x.
            - intros x1 y1 z1 J1 J2.
              applyAxiomII' J1; applyAxiomII' J2.
              rewrite J2; assumption.
            - apply AxiomII'.
              rewrite Lemma5_11. rewrite Lemma5_11.
              apply Lemma2 in I2.
              field. apply I2. }
          rewrite I3. apply Abs_R. lra.
Qed.

Lemma Lemma5_19 : ∀ c x0, limit {` λ _ y : R, y = c`} x0 c.
Proof.
  intros c x0. split.
  - apply Lemma5_10.
  - exists 2. split; [lra | split].
    + intros x H0. apply AxiomII.
      exists c. apply AxiomII'.
      reflexivity.
    + intros ε H0. exists 1.
      split; [lra | intros x H1].
      rewrite Lemma5_11. apply Abs_R.
      lra.
Qed.

Lemma Lemma7' : ∀ a c x0 n, limit
  {` λ x y, y = c * (x - a)^^n `} x0 (c * (x0 - a)^^n).
Proof.
  intros a c x0 n.
  assert (H0 : {` λ x y, y = c * (x - a)^^n `} =
    {` λ x y, y = c `} ** {` λ x y, y = (x - a)^^n `}).
  { apply AxiomI. intros [x y];
    split; intro I1;
    applyAxiomII' I1; apply AxiomII'.
    - repeat split.
      + apply AxiomII. exists c.
        apply AxiomII'. reflexivity.
      + apply AxiomII. exists ((x - a) ^^ n).
        apply AxiomII'. reflexivity.
      + rewrite Lemma5_11. rewrite Lemma4.
        assumption.
    - destruct I1 as [I1 [I2 I3]].
      rewrite I3. rewrite Lemma5_11.
      rewrite Lemma4. reflexivity. }
  rewrite H0. apply Theorem3_7_3.
  - apply Lemma5_19.
  - apply Lemma7.
Qed.

End A5_2.

Export A5_2.
