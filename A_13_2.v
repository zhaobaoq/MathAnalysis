Require Export A_13_1.

Module A13_2.

Theorem Theorem13_8 : ∀ fn a b x0 f c,
  IsSeq c -> a < x0 < b ->
  FunUniConF fn f (\(a, x0\) ∪ \(x0, b\)) ->
  (∀ n, limit fn[`n`] x0 c[n]) ->
  (∃ A, limit_seq c A /\ limit f x0 A).
Proof.
  intros fn a b x0 f c H0 H1 H2 H3.
  assert (H4 : Convergence c).
  { apply Theorem2_11; auto. intros ε I1.
    assert (I2 : ε/2 > 0). lra.
    assert (I3 : FunUniCon fn (\(a, x0\) ∪ \(x0, b\))).
    { exists f. assumption. }
    destruct H2 as [I4 [I5 [I6 [I7 I8]]]].
    generalize (Theorem13_1 fn (\(a, x0\) ∪ \(x0, b\)) I4 I7).
    intros [I9 I10]. clear I10. generalize (I9 I3); intros I10.
    clear I9. apply I10 in I2 as I11.
    destruct I11 as [N I11]. exists N.
    intros n m I12 I13. clear I10.
    apply NNPP. intros I14. apply Rnot_lt_ge in I14.
    assert (I15 : ∀ x, x ∈ \( a, x0 \) ∪ \( x0, b \) ->
      ε/4 <= Abs [(c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])]).
    { intros x J1.
      assert (J2 : (c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])
        = (c[n] - c[m]) - ((fn[`n`])[x] - (fn[`m`])[x])). field.
      rewrite J2. clear J2.
      generalize (Abs_abs_minus' (c[n] - c[m])
        ((fn[`n`])[x] - (fn[`m`])[x])). intros J2.
      apply Rle_trans with (r2 := Abs[c[n] - c[m]] -
        Abs[(fn[`n`])[x] - (fn[`m`])[x]]); auto.
      generalize (I11 m n x I13 I12 J1). lra. }
    generalize (H3 n). intros I16.
    generalize (H3 m). intros I17.
    assert (I18 : ε/8 > 0). lra.
    destruct I16 as [I16 [δ1' [I19 [I20 I21]]]].
    destruct I17 as [I22 [δ2' [I23 [I24 I25]]]].
    apply I21 in I18 as I26.
    destruct I26 as [δ1 [I26 I27]].
    apply I25 in I18 as I28.
    destruct I28 as [δ2 [I28 I29]].
    assert (I30 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2
      /\ δ < (x0 - a) /\ δ < (b - x0)).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - destruct (Rlt_or_le δ1 (x0-a)) as [K1 | K1].
        + destruct (Rlt_or_le δ1 (b-x0)) as [L1 | L1].
          * exists (δ1/2). lra.
          * exists ((b - x0)/2). lra.
        + destruct (Rlt_or_le (x0-a) (b-x0)) as [L1 | L1].
          * exists ((x0-a)/2). lra.
          * exists ((b-x0)/2). lra.
      - destruct (Rlt_or_le δ2 (x0-a)) as [K1 | K1].
        + destruct (Rlt_or_le δ2 (b-x0)) as [L1 | L1].
          * exists (δ2/2). lra.
          * exists ((b - x0)/2). lra.
        + destruct (Rlt_or_le (x0-a) (b-x0)) as [L1 | L1].
          * exists ((x0-a)/2). lra.
          * exists ((b-x0)/2). lra. }
    destruct I30 as [δ [I30 [I31 [I32 [I33 I34]]]]].
    assert (I35 : 0 < Abs[x0 + δ - x0] < δ1).
    { split.
      - apply Abs_not_eq_0. lra.
      - apply Abs_R. lra. }
    apply I27 in I35.
    assert (I36 : 0 < Abs[x0 + δ - x0] < δ2).
    { split.
      - apply Abs_not_eq_0. lra.
      - apply Abs_R. lra. }
    apply I29 in I36.
    assert (I37 : ∀ x y, Abs[x-y] = Abs[y-x]).
    { intros x y. rewrite <- (Ropp_minus_distr x y).
      apply Abs_eq_neg. }
    rewrite I37 in I35. rewrite I37 in I36.
    generalize (Abs_minus_le (c[n] - (fn[`n`])[x0 + δ])
      (c[m] - (fn[`m`])[x0 + δ])).
    intros I38.
    assert (I39 : x0 + δ ∈ \( a, x0 \) ∪ \( x0, b \)).
    { apply AxiomII. right.
      apply AxiomII. lra. }
    apply I15 in I39. lra. }
  destruct H4 as [A H4]. exists A. split; auto.
  destruct H2 as [H2 [H5 [H6 [H7 H8]]]].
  split; auto.
  assert (H9 : ∃ δ', δ' > 0 /\ δ' < x0 - a /\ δ' < b - x0).
  { destruct (Rlt_or_le (x0-a) (b-x0)) as [I1 | I1].
    - exists ((x0-a)/2). lra.
    - exists ((b-x0)/2). lra. }
  destruct H9 as [δ' [H9 [H10 H11]]].
  exists δ'. split; [assumption | split].
  - intros x I1. apply H6. applyAxiomII I1.
    apply Lemma2 in I1. apply AxiomII.
    assert (I2 : a < x < x0 \/ x0 < x < b). lra.
    destruct I2 as [I2 | I2].
    + left. apply AxiomII. lra.
    + right. apply AxiomII. lra.
  - intros ε I1. assert (I2 : ε/3 > 0). lra.
    apply H8 in I2 as I3.
    destruct I3 as [N1 I3].
    apply H4 in I2 as I4.
    destruct I4 as [N2 I4].
    generalize (Max_nat_2 N1 N2). intros [m [I5 I6]].
    apply I4 in I6.
    assert (I7 : ∀ x,  x ∈ \( a, x0 \) ∪ \( x0, b \)
      -> Abs[(fn[`m`])[x] - f[x]] < ε/3).
    { intros x J1. apply I3; auto. }
    generalize (H3 m). intros I8.
    unfold limit in I8.
    destruct I8 as [I8 [δ1 [I9 [I10 I11]]]].
    generalize (I11 (ε/3) I2).
    intros [δ2 [I12 I13]].
    assert (I14 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [K1 | K1].
        + exists (δ'/2). lra.
        + exists (δ2/2). lra.
      - destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
        + exists (δ1/2). lra.
        + exists (δ2/2). lra. }
    destruct I14 as [δ [I14 [I15 [I16 I17]]]].
    exists δ. split; try lra. intros x I18.
    assert (I19 : 0 < Abs[x - x0] < δ2). lra.
    apply I13 in I19.
    assert (I20 : x ∈ \( a, x0 \) ∪ \( x0, b \)).
    { apply AxiomII. apply Lemma2 in I18.
      assert (J1 : a < x < x0 \/ x0 < x < b). lra.
      destruct J1 as [J1 | J1].
      - left. apply AxiomII. lra.
      - right. apply AxiomII. lra. }
    apply I7 in I20. rewrite <- Ropp_minus_distr in I20.
    rewrite <- Abs_eq_neg in I20.
    assert (I21 : f[x] - A = f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m]) + (c[m] - A)). field.
    rewrite I21.
    generalize (Abs_plus_le (f[x] - fn[`m`][x])
      (fn[`m`][x] - c[m])). intros I22.
    generalize (Abs_plus_le (f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m])) (c[m] - A)). intros I23.
    lra.
Qed.

Theorem Theorem13_8_1 : ∀ fn b x0 f c,
  IsSeq c -> x0 < b ->
  FunUniConF fn f (\(x0, b\)) ->
  (∀ n, limit_pos fn[`n`] x0 c[n]) ->
  (∃ A, limit_seq c A /\ limit_pos f x0 A).
Proof.
  intros fn b x0 f c H0 H1 H2 H3.
  assert (H4 : Convergence c).
  { apply Theorem2_11; auto. intros ε I1.
    assert (I2 : ε/2 > 0). lra.
    assert (I3 : FunUniCon fn (\(x0, b\))).
    { exists f. assumption. }
    destruct H2 as [I4 [I5 [I6 [I7 I8]]]].
    generalize (Theorem13_1 fn (\(x0, b\)) I4 I7).
    intros [I9 I10]. clear I10. generalize (I9 I3); intros I10.
    clear I9. apply I10 in I2 as I11.
    destruct I11 as [N I11]. exists N.
    intros n m I12 I13. clear I10.
    apply NNPP. intros I14. apply Rnot_lt_ge in I14.
    assert (I15 : ∀ x, x ∈ \( x0, b \) ->
      ε/4 <= Abs [(c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])]).
    { intros x J1.
      assert (J2 : (c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])
        = (c[n] - c[m]) - ((fn[`n`])[x] - (fn[`m`])[x])). field.
      rewrite J2. clear J2.
      generalize (Abs_abs_minus' (c[n] - c[m])
        ((fn[`n`])[x] - (fn[`m`])[x])). intros J2.
      apply Rle_trans with (r2 := Abs[c[n] - c[m]] -
        Abs[(fn[`n`])[x] - (fn[`m`])[x]]); auto.
      generalize (I11 m n x I13 I12 J1). lra. }
    generalize (H3 n). intros I16.
    generalize (H3 m). intros I17.
    assert (I18 : ε/8 > 0). lra.
    destruct I16 as [I16 [δ1' [I19 [I20 I21]]]].
    destruct I17 as [I22 [δ2' [I23 [I24 I25]]]].
    apply I21 in I18 as I26.
    destruct I26 as [δ1 [I26 I27]].
    apply I25 in I18 as I28.
    destruct I28 as [δ2 [I28 I29]].
    assert (I30 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2
      /\ δ < (b - x0)).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - destruct (Rlt_or_le δ1 (b-x0)) as [K1 | K1].
        + exists (δ1/2). lra.
        + exists ((b-x0)/2). lra.
      - destruct (Rlt_or_le δ2 (b-x0)) as [K1 | K1].
        + exists (δ2/2). lra.
        + exists ((b-x0)/2). lra. }
    destruct I30 as [δ [I30 [I31 [I32 I33]]]].
    assert (I35 : x0 < x0 + δ < x0 + δ1). lra.
    apply I27 in I35.
    assert (I36 : x0 < x0 + δ < x0 + δ2). lra.
    apply I29 in I36.
    assert (I37 : ∀ x y, Abs[x-y] = Abs[y-x]).
    { intros x y. rewrite <- (Ropp_minus_distr x y).
      apply Abs_eq_neg. }
    rewrite I37 in I35. rewrite I37 in I36.
    generalize (Abs_minus_le (c[n] - (fn[`n`])[x0 + δ])
      (c[m] - (fn[`m`])[x0 + δ])).
    intros I38.
    assert (I39 : x0 + δ ∈ \( x0, b \)).
    { apply AxiomII. lra. }
    apply I15 in I39. lra. }
  destruct H4 as [A H4]. exists A. split; auto.
  destruct H2 as [H2 [H5 [H6 [H7 H8]]]].
  split; auto.
  assert (H9 : ∃ δ', δ' > 0 /\ δ' < b - x0).
  { exists ((b-x0)/2). lra. }
  destruct H9 as [δ' [H9 H10]].
  exists δ'. split; [assumption | split].
  - intros x I1. apply H6. applyAxiomII I1.
    apply AxiomII.
    assert (I2 : x0 < x < b). lra.
    lra.
  - intros ε I1. assert (I2 : ε/3 > 0). lra.
    apply H8 in I2 as I3.
    destruct I3 as [N1 I3].
    apply H4 in I2 as I4.
    destruct I4 as [N2 I4].
    generalize (Max_nat_2 N1 N2). intros [m [I5 I6]].
    apply I4 in I6.
    assert (I7 : ∀ x,  x ∈ \( x0, b \)
      -> Abs[(fn[`m`])[x] - f[x]] < ε/3).
    { intros x J1. apply I3; auto. }
    generalize (H3 m). intros I8.
    unfold limit in I8.
    destruct I8 as [I8 [δ1 [I9 [I10 I11]]]].
    generalize (I11 (ε/3) I2).
    intros [δ2 [I12 I13]].
    assert (I14 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [K1 | K1].
        + exists (δ'/2). lra.
        + exists (δ2/2). lra.
      - destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
        + exists (δ1/2). lra.
        + exists (δ2/2). lra. }
    destruct I14 as [δ [I14 [I15 [I16 I17]]]].
    exists δ. split; try lra. intros x I18.
    assert (I19 : x0 < x < x0 + δ2). lra.
    apply I13 in I19.
    assert (I20 : x ∈ \( x0, b \)).
    { apply AxiomII. lra. }
    apply I7 in I20. rewrite <- Ropp_minus_distr in I20.
    rewrite <- Abs_eq_neg in I20.
    assert (I21 : f[x] - A = f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m]) + (c[m] - A)). field.
    rewrite I21.
    generalize (Abs_plus_le (f[x] - fn[`m`][x])
      (fn[`m`][x] - c[m])). intros I22.
    generalize (Abs_plus_le (f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m])) (c[m] - A)). intros I23.
    lra.
Qed.

Theorem Theorem13_8_2 : ∀ fn a x0 f c,
  IsSeq c -> a < x0 ->
  FunUniConF fn f (\(a, x0\)) ->
  (∀ n, limit_neg fn[`n`] x0 c[n]) ->
  (∃ A, limit_seq c A /\ limit_neg f x0 A).
Proof.
  intros fn a x0 f c H0 H1 H2 H3.
  assert (H4 : Convergence c).
  { apply Theorem2_11; auto. intros ε I1.
    assert (I2 : ε/2 > 0). lra.
    assert (I3 : FunUniCon fn (\(a, x0\))).
    { exists f. assumption. }
    destruct H2 as [I4 [I5 [I6 [I7 I8]]]].
    generalize (Theorem13_1 fn (\(a, x0\)) I4 I7).
    intros [I9 I10]. clear I10. generalize (I9 I3); intros I10.
    clear I9. apply I10 in I2 as I11.
    destruct I11 as [N I11]. exists N.
    intros n m I12 I13. clear I10.
    apply NNPP. intros I14. apply Rnot_lt_ge in I14.
    assert (I15 : ∀ x, x ∈ \( a, x0 \) ->
      ε/4 <= Abs [(c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])]).
    { intros x J1.
      assert (J2 : (c[n] - (fn[`n`])[x]) - (c[m] - (fn[`m`])[x])
        = (c[n] - c[m]) - ((fn[`n`])[x] - (fn[`m`])[x])). field.
      rewrite J2. clear J2.
      generalize (Abs_abs_minus' (c[n] - c[m])
        ((fn[`n`])[x] - (fn[`m`])[x])). intros J2.
      apply Rle_trans with (r2 := Abs[c[n] - c[m]] -
        Abs[(fn[`n`])[x] - (fn[`m`])[x]]); auto.
      generalize (I11 m n x I13 I12 J1). lra. }
    generalize (H3 n). intros I16.
    generalize (H3 m). intros I17.
    assert (I18 : ε/8 > 0). lra.
    destruct I16 as [I16 [δ1' [I19 [I20 I21]]]].
    destruct I17 as [I22 [δ2' [I23 [I24 I25]]]].
    apply I21 in I18 as I26.
    destruct I26 as [δ1 [I26 I27]].
    apply I25 in I18 as I28.
    destruct I28 as [δ2 [I28 I29]].
    assert (I30 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2
      /\ δ < (x0 - a)).
    { destruct (Rlt_or_le δ1 δ2) as [J1 | J1].
      - destruct (Rlt_or_le δ1 (x0-a)) as [K1 | K1].
        + exists (δ1/2). lra.
        + exists ((x0-a)/2). lra.
      - destruct (Rlt_or_le δ2 (x0-a)) as [K1 | K1].
        + exists (δ2/2). lra.
        + exists ((x0-a)/2). lra. }
    destruct I30 as [δ [I30 [I31 [I32 I33]]]].
    assert (I35 : x0 - δ1 < x0 - δ < x0). lra.
    apply I27 in I35.
    assert (I36 : x0 - δ2 < x0 - δ < x0). lra.
    apply I29 in I36.
    assert (I37 : ∀ x y, Abs[x-y] = Abs[y-x]).
    { intros x y. rewrite <- (Ropp_minus_distr x y).
      apply Abs_eq_neg. }
    rewrite I37 in I35. rewrite I37 in I36.
    generalize (Abs_minus_le (c[n] - (fn[`n`])[x0 - δ])
      (c[m] - (fn[`m`])[x0 - δ])).
    intros I38.
    assert (I39 : x0 - δ ∈ \( a, x0 \)).
    { apply AxiomII. lra. }
    apply I15 in I39. lra. }
  destruct H4 as [A H4]. exists A. split; auto.
  destruct H2 as [H2 [H5 [H6 [H7 H8]]]].
  split; auto.
  assert (H9 : ∃ δ', δ' > 0 /\ δ' < x0 - a).
  { exists ((x0-a)/2). lra. }
  destruct H9 as [δ' [H9 H10]].
  exists δ'. split; [assumption | split].
  - intros x I1. apply H6. applyAxiomII I1.
    apply AxiomII.
    assert (I2 : a < x < x0). lra.
    lra.
  - intros ε I1. assert (I2 : ε/3 > 0). lra.
    apply H8 in I2 as I3.
    destruct I3 as [N1 I3].
    apply H4 in I2 as I4.
    destruct I4 as [N2 I4].
    generalize (Max_nat_2 N1 N2). intros [m [I5 I6]].
    apply I4 in I6.
    assert (I7 : ∀ x,  x ∈ \( a, x0 \)
      -> Abs[(fn[`m`])[x] - f[x]] < ε/3).
    { intros x J1. apply I3; auto. }
    generalize (H3 m). intros I8.
    unfold limit in I8.
    destruct I8 as [I8 [δ1 [I9 [I10 I11]]]].
    generalize (I11 (ε/3) I2).
    intros [δ2 [I12 I13]].
    assert (I14 : ∃ δ, δ > 0 /\ δ < δ' /\ δ < δ1 /\ δ < δ2).
    { destruct (Rlt_or_le δ' δ1) as [J1 | J1].
      - destruct (Rlt_or_le δ' δ2) as [K1 | K1].
        + exists (δ'/2). lra.
        + exists (δ2/2). lra.
      - destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
        + exists (δ1/2). lra.
        + exists (δ2/2). lra. }
    destruct I14 as [δ [I14 [I15 [I16 I17]]]].
    exists δ. split; try lra. intros x I18.
    assert (I19 : x0 - δ2 < x < x0). lra.
    apply I13 in I19.
    assert (I20 : x ∈ \( a, x0 \)).
    { apply AxiomII. lra. }
    apply I7 in I20. rewrite <- Ropp_minus_distr in I20.
    rewrite <- Abs_eq_neg in I20.
    assert (I21 : f[x] - A = f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m]) + (c[m] - A)). field.
    rewrite I21.
    generalize (Abs_plus_le (f[x] - fn[`m`][x])
      (fn[`m`][x] - c[m])). intros I22.
    generalize (Abs_plus_le (f[x] - fn[`m`][x] +
      (fn[`m`][x] - c[m])) (c[m] - A)). intros I23.
    lra.
Qed.

Theorem Theorem13_9 : ∀ fn f a b,
  a < b -> FunUniConF fn f \(a, b\) ->
  (∀ n, ContinuousOpen fn[`n`] a b) ->
  ContinuousOpen f a b.
Proof.
  intros fn f a b H0 H1 H2 x0 H3.
  assert (H4 : ∃ c, c = {` λ n s, s = fn[`n`][x0] `}).
  { exists {` λ n s, s = fn[`n`][x0] `}.
    reflexivity. }
  destruct H4 as [c H4].
  assert (H5 : FunUniConF fn f (\(a, x0\) ∪ \(x0, b\))).
  { eapply Lemma13_1_1; try apply H1.
    intros x I1. apply AxiomII.
    applyAxiomII I1.
    destruct I1 as [I1 | I1]; applyAxiomII I1; lra. }
  assert (H7 : IsSeq c).
  { rewrite H4. apply FunIsSeq. }
  assert (H8 : ∀ n, limit fn[`n`] x0 c[n]).
  { intros n. generalize (H2 n x0 H3); intros [J1 J2].
    rewrite H4. rewrite FunValueR. assumption. }
  generalize (Theorem13_8 fn a b x0 f c H7 H3 H5 H8).
  intros [A [H9 H10]].
  assert (H12 : limit_seq c f[x0]).
  { split; auto. intros ε I9.
    apply H1 in I9 as [N I9].
    exists N. intros n J1.
    rewrite H4. rewrite FunValueR.
    apply I9; [auto | apply AxiomII]; lra. }
  assert (H13 : f[x0] = A).
  { eapply Theorem2_2; eauto. }
  rewrite <- H13 in H10.
  split; auto. apply H1.
  apply AxiomII. assumption.
Qed.

Theorem Theorem13_9' : ∀ fn f a b,
  a < b -> FunUniConF fn f (\[a, b\]) ->
  (∀ n, ContinuousClose fn[`n`] a b) ->
  ContinuousClose f a b.
Proof.
  intros fn f a b H0 H1 H2.
  assert (H3 : FunUniConF fn f (\(a, b\))).
  { eapply Lemma13_1_1; eauto.
    intros x J1. apply AxiomII.
    applyAxiomII J1. lra. }
  split; [idtac | split].
  - eapply Theorem13_9; eauto.
    intros n x I1. apply H2. assumption.
  - destruct H1 as [I1 [I2 [I3 [I4 I5]]]].
    assert (I6 : a ∈ dom[f]).
    { apply I3. apply AxiomII. lra. }
    split; auto.
    assert (I7 : ∃ c, c = {` λ n s, s = fn[`n`][a] `}).
    { exists {` λ n s, s = fn[`n`][a] `}.
      reflexivity. }
    destruct I7 as [c I7].
    assert (I8 : IsSeq c).
    { rewrite I7. apply FunIsSeq. }
    assert (I9 : limit_seq c f[a]).
    { split; auto. intros ε I9.
      apply I5 in I9 as [N I9].
      exists N. intros n J1.
      rewrite I7. rewrite FunValueR.
      apply I9; [auto | apply AxiomII]; lra. }
    assert (I11 : ∀ n, limit_pos fn[`n`] a c[n]).
    { intros n. generalize (H2 n); intros [J1 [J2 J3]].
      rewrite I7. rewrite FunValueR. apply J2. }
    generalize (Theorem13_8_1 fn b a f c I8 H0 H3 I11).
    intros [A [I12 I13]].
    assert (I14 : f[a] = A).
    { eapply Theorem2_2; eauto. }
    rewrite I14. assumption.
  - destruct H1 as [I1 [I2 [I3 [I4 I5]]]].
    assert (I6 : b ∈ dom[f]).
    { apply I3. apply AxiomII. lra. }
    split; auto.
    assert (I7 : ∃ c, c = {` λ n s, s = fn[`n`][b] `}).
    { exists {` λ n s, s = fn[`n`][b] `}.
      reflexivity. }
    destruct I7 as [c I7].
    assert (I8 : IsSeq c).
    { rewrite I7. apply FunIsSeq. }
    assert (I9 : limit_seq c f[b]).
    { split; auto. intros ε I9.
      apply I5 in I9 as [N I9].
      exists N. intros n J1.
      rewrite I7. rewrite FunValueR.
      apply I9; [auto | apply AxiomII]; lra. }
    assert (I11 : ∀ n, limit_neg fn[`n`] b c[n]).
    { intros n. generalize (H2 n); intros [J1 [J2 J3]].
      rewrite I7. rewrite FunValueR. apply J3. }
    generalize (Theorem13_8_2 fn a b f c I8 H0 H3 I11).
    intros [A [I12 I13]].
    assert (I14 : f[b] = A).
    { eapply Theorem2_2; eauto. }
    rewrite I14. assumption.
Qed.

Theorem Theorem13_9'' : ∀ fn f a b,
  a < b -> FunCloseUniConF fn f \(a, b\) ->
  (∀ n, ContinuousOpen fn[`n`] a b) ->
  ContinuousOpen f a b.
Proof.
  intros fn f a b H0 H1 H2 x0 H3.
  assert (H4 : (\[(a + x0)/2, (x0 + b)/2 \]) ⊂ \( a, b \)).
  { intros x I1. applyAxiomII I1.
    apply AxiomII. lra. }
  apply H1 in H4 as H5.
  assert (H6 : \((a + x0)/2, (x0 + b)/2 \)
    ⊂ (\[(a + x0)/2, (x0 + b)/2 \])).
  { intros x I1. applyAxiomII I1.
    apply AxiomII. lra. }
  assert (H7 : FunUniConF fn f \((a + x0)/2, (x0 + b)/2 \)).
  { eapply Lemma13_1_1; eauto. }
  assert (H8 : ∀ n, ContinuousOpen fn[`n`]
    ((a + x0)/2) ((x0 + b)/2)).
  { intros n x I1. apply H2. lra. }
  assert (H9 : (a + x0)/2 < (x0 + b)/2). lra.
  generalize (Theorem13_9 fn f ((a + x0)/2)
    ((x0 + b)/2) H9 H7 H8). intros H10.
  apply H10. lra.
Qed.

Lemma Lemma13_2_1 : ∀ u a b, a < b ->
  (∀ n, ContinuousOpen u[`n`] a b) ->
  (∀ n, ContinuousOpen (FunSer u)[`n`] a b).
Proof.
  intros u a b H0 H1 n.
  induction n as [|n IHn].
  - generalize (H1 O). intros H2.
    intros x I1. apply H2 in I1 as I2.
    destruct I2 as [I2 [I3 [δ' [I4 [I5 I6]]]]].
    split. apply FunSerDom.
    rewrite VFunSerNX. simpl.
    rewrite VFunSeqN.
    assert (I7 : Function (FunSer u)[`0%nat`]).
    { rewrite VFunSerN. apply IsFun. }
    split; auto. exists δ'. repeat split; auto.
    + intros x0 J1. apply FunSerDom.
    + intros ε J1. apply I6 in J1 as [δ [J2 J3]].
      exists δ. split; auto.
      intros x1 J4. rewrite VFunSerNX.
      simpl. rewrite VFunSeqN. apply J3; assumption.
  - generalize (H1 (S n)). intros I1.
    intros x0 J1.
    apply IHn in J1 as J2. apply I1 in J1 as J3.
    rewrite VFunSerN in J2.
    split; try apply FunSerDom.
    rewrite VFunSerNX. simpl.
    rewrite VFunSeqN. rewrite VFunSerN.
    split; try apply IsFun.
    destruct J2 as [J2 [J7 [δ1' [J4 [J5 J6]]]]].
    destruct J3 as [J3 [J11 [δ2' [J8 [J9 J10]]]]].
    exists δ1'. split; auto. split.
    + intros x K1. rewrite <- VFunSerN.
      apply FunSerDom.
    + intros ε K12.
      assert (K1 : ε/2 > 0). lra.
      apply J6 in K1 as K2.
      apply J10 in K1 as K3.
      clear J6 J10.
      destruct K2 as [δ1 [[K2 K6] K4]].
      destruct K3 as [δ2 [[K3 K7] K5]].
      generalize (Lemma1 δ1 δ2 K2 K3).
      intros [δ [K8 [K9 K10]]].
      exists δ. split; [lra | intros x K11].
      assert (K13 : 0 < Abs[x - x0] < δ1). lra.
      assert (K14 : 0 < Abs[x - x0] < δ2). lra.
      apply K4 in K13. apply K5 in K14.
      clear K4 K5.
      repeat rewrite FunValueR in *.
      assert (K15 : Σ (VFunSeq u x) (S n) -
        (Σ (VFunSeq u x0) n + (u[`S n`])[x0]) =
        Σ (VFunSeq u x) n - Σ (VFunSeq u x0) n
        + ((u[`S n`])[x] - (u[`S n`])[x0])).
      { simpl. rewrite VFunSeqN. field. }
      rewrite K15. clear K15.
      generalize (Abs_plus_le (Σ (VFunSeq u x) n
        - Σ (VFunSeq u x0) n)
        ((u[`S n`])[x] - (u[`S n`])[x0])). lra.
Qed.

Lemma Lemma13_2_2 : ∀ u a b, a < b ->
  (∀ n, ContinuousClose u[`n`] a b) ->
  (∀ n, ContinuousClose (FunSer u)[`n`] a b).
Proof.
  intros u a b H0 H1 n.
  split. apply Lemma13_2_1; auto.
  intros m. apply H1.
  induction n as [|n IHn].
  - generalize (H1 O). intros [H2 [H3 H4]].
    split.
    + split; try apply FunSerDom.
      rewrite VFunSerNX. simpl. rewrite VFunSeqN.
      split.
      * rewrite VFunSerN. apply IsFun.
      * destruct H3 as [I1 [ I2 [δ' [I3 [I4 I5]]]]].
        exists δ'. repeat split; auto.
        -- intros x J1. apply FunSerDom.
        -- intros ε J1. apply I5 in J1 as [δ [J1 J2]].
          exists δ. split; auto. intros x J3.
          rewrite VFunSerNX. simpl. rewrite VFunSeqN.
          apply J2. assumption.
    + split; try apply FunSerDom.
      rewrite VFunSerNX. simpl. rewrite VFunSeqN.
      split.
      * rewrite VFunSerN. apply IsFun.
      * destruct H4 as [I1 [ I2 [δ' [I3 [I4 I5]]]]].
        exists δ'. repeat split; auto.
        -- intros x J1. apply FunSerDom.
        -- intros ε J1. apply I5 in J1 as [δ [J1 J2]].
          exists δ. split; auto. intros x J3.
          rewrite VFunSerNX. simpl. rewrite VFunSeqN.
          apply J2. assumption.
  - generalize (H1 (S n)). intros [I1 [I2 I3]].
    destruct IHn as [I5 I6].
    split.
    + split; try apply FunSerDom.
      rewrite VFunSerNX. simpl.
      rewrite VFunSeqN. rewrite VFunSerN.
      split; try apply IsFun.
      destruct I5 as [J2 [J7 [δ1' [J4 [J5 J6]]]]].
      destruct I2 as [J3 [J11 [δ2' [J8 [J9 J10]]]]].
      exists δ1'. split; auto. split.
      * intros x K1. rewrite <- VFunSerN.
        apply FunSerDom.
      * intros ε K12.
        assert (K1 : ε/2 > 0). lra.
        apply J6 in K1 as K2.
        apply J10 in K1 as K3.
        clear J6 J10.
        destruct K2 as [δ1 [[K2 K6] K4]].
        destruct K3 as [δ2 [[K3 K7] K5]].
        generalize (Lemma1 δ1 δ2 K2 K3).
        intros [δ [K8 [K9 K10]]].
        exists δ. split; [lra | intros x K11].
        assert (K13 : a < x < a + δ1). lra.
        assert (K14 : a < x < a + δ2). lra.
        apply K4 in K13. apply K5 in K14.
        clear K4 K5.
        repeat rewrite FunValueR in *.
        assert (K15 : Σ (VFunSeq u x) (S n) -
          (Σ (VFunSeq u a) n + (u[`S n`])[a]) =
          Σ (VFunSeq u x) n - Σ (VFunSeq u a) n
          + ((u[`S n`])[x] - (u[`S n`])[a])).
        { simpl. rewrite VFunSeqN. field. }
        rewrite K15. clear K15.
        repeat rewrite VFunSerNX in K13.
        generalize (Abs_plus_le (Σ (VFunSeq u x) n
          - Σ (VFunSeq u a) n)
          ((u[`S n`])[x] - (u[`S n`])[a])). lra.
    + split; try apply FunSerDom.
      rewrite VFunSerNX. simpl.
      rewrite VFunSeqN. rewrite VFunSerN.
      split; try apply IsFun.
      destruct I6 as [J2 [J7 [δ1' [J4 [J5 J6]]]]].
      destruct I3 as [J3 [J11 [δ2' [J8 [J9 J10]]]]].
      exists δ1'. split; auto. split.
      * intros x K1. rewrite <- VFunSerN.
        apply FunSerDom.
      * intros ε K12.
        assert (K1 : ε/2 > 0). lra.
        apply J6 in K1 as K2.
        apply J10 in K1 as K3.
        clear J6 J10.
        destruct K2 as [δ1 [[K2 K6] K4]].
        destruct K3 as [δ2 [[K3 K7] K5]].
        generalize (Lemma1 δ1 δ2 K2 K3).
        intros [δ [K8 [K9 K10]]].
        exists δ. split; [lra | intros x K11].
        assert (K13 : b - δ1 < x < b). lra.
        assert (K14 : b - δ2 < x < b). lra.
        apply K4 in K13. apply K5 in K14.
        clear K4 K5.
        repeat rewrite FunValueR in *.
        assert (K15 : Σ (VFunSeq u x) (S n) -
          (Σ (VFunSeq u b) n + (u[`S n`])[b]) =
          Σ (VFunSeq u x) n - Σ (VFunSeq u b) n
          + ((u[`S n`])[x] - (u[`S n`])[b])).
        { simpl. rewrite VFunSeqN. field. }
        rewrite K15. clear K15.
        repeat rewrite VFunSerNX in K13.
        generalize (Abs_plus_le (Σ (VFunSeq u x) n
          - Σ (VFunSeq u b) n)
          ((u[`S n`])[x] - (u[`S n`])[b])). lra.
Qed.

Theorem Theorem13_12 : ∀ u S a b,
  a < b -> FunSerUniConF u S (\(a, b\)) ->
  (∀ n, ContinuousOpen u[`n`] a b) ->
  ContinuousOpen S a b.
Proof.
  intros u S a b H0 H1 H2.
  apply Theorem13_9 with (fn := (FunSer u)); auto.
  - apply Lemma13_1_2; auto.
  - apply Lemma13_2_1; auto.
Qed.

Theorem Theorem13_12' : ∀ u S a b,
  a < b -> FunSerUniConF u S (\[a, b\]) ->
  (∀ n, ContinuousClose u[`n`] a b) ->
  ContinuousClose S a b.
Proof.
  intros u S a b H0 H1 H2.
  apply Theorem13_9' with (fn := (FunSer u)); auto.
  - apply Lemma13_1_2; auto.
  - apply Lemma13_2_2; auto.
Qed.

Theorem Theorem13_12'' : ∀ u S a b,
  a < b -> FunSerCloseUniConF u S (\(a, b\)) ->
  (∀ n, ContinuousOpen u[`n`] a b) ->
  ContinuousOpen S a b.
Proof.
  intros u S a b H0 H1 H2.
  apply Theorem13_9'' with (fn := (FunSer u)); auto.
  - apply Lemma13_1_6; auto.
  - apply Lemma13_2_1; auto.
Qed.

End A13_2.

Export A13_2.