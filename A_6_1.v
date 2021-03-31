Require Export A_5_4.

Module A6_1.

(* 罗尔定理 *)
Theorem Theorem6_1 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∀ x, a < x < b -> derivable f x)
  -> f[a] = f[b]
  -> ∃ ξ, a < ξ < b /\ derivative f ξ 0.
Proof.
  intros f a b H0 H1 H2 H3.
  generalize (Theorem4_6 f a b H0 H1).
  intros [[M [H4 [H5 [ξ1 [H6 H10]]]]] [m [H7 [H8 [ξ2 [H9 H11]]]]]].
  assert (H12 : m <= M).
  { assert (I1 : a ∈ \[ a, b \]).
    { apply AxiomII. lra. }
    apply H5 in I1 as I2. apply H8 in I1 as I3. lra. }
  destruct H12 as [H12 | H12].
  - assert (I1 : a < ξ1 < b \/ a < ξ2 < b).
    { apply NNPP. intro J1. apply not_or_and in J1 as [J1 J2].
      applyAxiomII H6. applyAxiomII H9.
      assert (J3 : ξ1 = a \/ ξ1 = b). lra.
      assert (J4 : ξ2 = a \/ ξ2 = b). lra.
      destruct J3 as [J3 | J3]; rewrite J3 in *;
      destruct J4 as [J4 | J4]; rewrite J4 in *; lra. }
    destruct I1 as [I1 | I1].
    + exists ξ1. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * left. unfold localMax. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ1 - a /\ δ < b - ξ1).
        { destruct (Rlt_or_le (ξ1 - a) (b - ξ1)) as [J1 | J1].
          - exists ((ξ1 - a) / 2). repeat split; lra.
          - exists ((b - ξ1) / 2). repeat split; lra. }
        destruct J1 as [δ [J1 [J2 J3]]].
        exists δ. repeat split; auto.
        -- intros x K1. applyAxiomII K1.
          apply H4. apply AxiomII. apply Abs_R in K1. lra.
        -- intros x K1. applyAxiomII K1. apply Abs_R in K1.
          rewrite H10. apply H5. apply AxiomII. lra.
    + exists ξ2. split; auto. apply Theorem5_3.
      * apply H2; assumption.
      * right. unfold localMin. split; try apply H1.
        assert (J1 : ∃ δ, δ > 0 /\ δ < ξ2 - a /\ δ < b - ξ2).
        { destruct (Rlt_or_le (ξ2 - a) (b - ξ2)) as [J1 | J1].
          - exists ((ξ2 - a) / 2). repeat split; lra.
          - exists ((b - ξ2) / 2). repeat split; lra. }
        destruct J1 as [δ [J1 [J2 J3]]].
        exists δ. repeat split; auto.
        -- intros x K1. applyAxiomII K1.
          apply H4. apply AxiomII. apply Abs_R in K1. lra.
        -- intros x K1. applyAxiomII K1. apply Abs_R in K1.
          rewrite H11. apply H8. apply AxiomII. lra.
  - assert (I1 : ∀ x, x ∈ \[ a, b \] -> f[x] = m).
    { intros x J1. apply H5 in J1 as J2.
      apply H8 in J1 as J3. lra. }
    exists ((a + b) / 2). split; try lra.
    apply Theorem5_3.
    + apply H2; lra.
    + left. unfold localMax. split; try apply H1.
      exists ((b - a) / 2). repeat split; try lra.
      * intros x J1. applyAxiomII J1. apply H4.
        apply Abs_R in J1. apply AxiomII. lra.
      * intros x J1. applyAxiomII J1. apply Abs_R in J1.
        rewrite I1. rewrite I1. lra.
        -- apply AxiomII. lra.
        -- apply AxiomII. lra.
Qed.

(* 拉格朗日中值定理 *)
Theorem Theorem6_2 : ∀ (f : Fun) (a b : R), a < b
  -> ContinuousClose f a b
  -> (∀ x, a < x < b -> derivable f x)
  -> ∃ ξ, a < ξ < b /\ derivative f ξ ((f[b] - f[a]) / (b - a)).
Proof.
  intros f a b H0 H1 H2.
  assert (H3 : ∃ F, F = {` λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a) `}).
  { exists {` λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a) `}; reflexivity. }
  destruct H3 as [F H3].
  assert (H4 : Function F).
  { rewrite H3. unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    rewrite I2. assumption. }
  assert (H5 : ∀ x, F[x] = f[x] - f[a]
    - (f[b] - f[a])/(b - a)*(x - a)).
  { intro x. apply f_x; auto. rewrite H3. apply AxiomII'.
    reflexivity. }
  destruct H1 as [H1 [H6 H7]].
  unfold ContinuousOpen in H1.
  assert (H8 : ContinuousClose F a b).
  { unfold ContinuousClose. split; [idtac | split].
    - unfold ContinuousOpen. intros x I1.
      unfold Continuous. split.
      + apply AxiomII. exists (f[x] - f[a]
          - (f[b] - f[a])/(b - a)*(x - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit. split; auto. apply H1 in I1 as I2.
        unfold Continuous in I2. destruct I2 as [I2 I3].
        unfold limit in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,0 < Abs [x0 - x] < δ2 ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - x)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K3; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K3. clear K5.
                assert (K5 : Abs [x0 - x] * (Abs [f [b] - f [a]] / (b - a))
                  = Abs [f [b] - f [a]] / (b - a) * Abs [x0 - x]).
                { field. lra. }
                rewrite K5 in K3. assumption. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [x] - f [a]
            - (f [b] - f [a]) / (b - a) * (x - a))
            = f[x0] - f[x] - (f [b] - f [a]) / (b - a) * (x0 - x)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[x])
            ((f [b] - f [a]) / (b - a) * (x0 - x))).
          intros J11. assert (J12 : 0 < Abs [x0 - x] < δ1). lra.
          apply J4 in J12. assert (J13 : 0 < Abs [x0 - x] < δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousRight. split.
      + apply AxiomII. exists (f[a] - f[a]
          - (f[b] - f[a])/(b - a)*(a - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit_pos. split; auto.
        unfold ContinuousRight in H6. destruct H6 as [I2 I3].
        unfold limit_pos in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,a < x0 < a + δ2 ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - a)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                assert (K6 : x0 - a < ε / 2 * ((b - a)
                  / Abs [f [b] - f [a]])). lra.
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K6; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K6. clear K5.
                rewrite (Abs_gt (x0 - a)); lra. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [a] - f [a]
            - (f [b] - f [a]) / (b - a) * (a - a))
            = f[x0] - f[a] - (f [b] - f [a]) / (b - a) * (x0 - a)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[a])
            ((f [b] - f [a]) / (b - a) * (x0 - a))).
          intros J11. assert (J12 : a < x0 < a + δ1). lra.
          apply J4 in J12. assert (J13 : a < x0 < a + δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousLeft. split.
      + apply AxiomII. exists (f[b] - f[a]
          - (f[b] - f[a])/(b - a)*(b - a)).
        rewrite H3. apply AxiomII'. reflexivity.
      + unfold limit_neg. split; auto.
        unfold ContinuousLeft in H7. destruct H7 as [I2 I3].
        unfold limit_neg in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(b - a)*(x0 - a)).
          rewrite H3. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0, b - δ2 < x0 < b ->
            Abs[(f [b] - f [a]) / (b - a) * (x0 - b)] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - exists ((ε / 2 * ((b - a) / Abs [f [b] - f [a]] ))).
              split.
              + apply Rmult_lt_0_compat; auto.
                apply Rdiv_lt_0_compat; try lra.
                apply Abs_not_eq_0; auto.
              + intros x0 K2. rewrite Abs_mult. rewrite Abs_div; try lra.
                rewrite (Abs_gt (b - a)); try lra.
                destruct K2 as [K2 K3].
                assert (K4 : 0 < Abs [f [b] - f [a]] / (b - a)).
                { apply Rdiv_lt_0_compat; try lra.
                  apply Abs_not_eq_0; auto. }
                assert (K6 : b - x0 < ε / 2 * ((b - a)
                  / Abs [f [b] - f [a]])). lra.
                apply Rmult_lt_compat_r with
                  (r := Abs [f [b] - f [a]] / (b - a)) in K6; auto.
                assert (K5 : ε / 2 * ((b - a) / Abs [f [b] - f [a]]) *
                  (Abs [f [b] - f [a]] / (b - a)) = ε / 2).
                { apply Abs_not_eq_0 in K1. field; split; lra. }
                rewrite K5 in K6. clear K5.
                rewrite (Abs_lt (x0 - b)); lra. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). split; lra.
            - exists (δ2 / 2). split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          rewrite H5. rewrite H5.
          assert (J11 : f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [b] - f [a]
            - (f [b] - f [a]) / (b - a) * (b - a))
            = f[x0] - f[b] - (f [b] - f [a]) / (b - a) * (x0 - b)).
          { field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[b])
            ((f [b] - f [a]) / (b - a) * (x0 - b))).
          intros J11. assert (J12 : b - δ1 < x0 < b). lra.
          apply J4 in J12. assert (J13 : b - δ2 < x0 < b).
          lra. apply J6 in J13. lra. }
  assert (H9 : ∀ x, a < x < b -> derivable F x).
  { intros x I1. apply H2 in I1 as I2.
    destruct I2 as [y' [I2 [[δ' [I3 I4]] I5]]].
    exists (y' - (f [b] - f [a]) / (b - a)).
    split; auto. split.
    - exists δ'. split; auto. intros x0 J1.
      apply AxiomII. rewrite H3.
      exists (f [x0] - f [a] - (f [b] - f [a]) / (b - a) * (x0 - a)).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct I5 as [I5 [δ0' [I6 [I7 I8]]]].
      split.
      + unfold Function. intros x0 y0 z0 J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + exists δ0'. split; auto. split.
        * intros x0 J1. apply AxiomII.
          exists ((F [x0] - F [x]) / (x0 - x)).
          apply AxiomII'. reflexivity.
        * intros ε J1. apply I8 in J1 as J2.
          destruct J2 as [δ [J2 J3]]. exists δ. split; auto.
          intros x0 J4. apply J3 in J4 as J5.
          assert (J6 : {` λ x0 y, y =
            (f [x0] - f [x]) / (x0 - x) `} [x0]
            = (f [x0] - f [x]) / (x0 - x)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : {` λ x1 y, y = (F [x1] - F [x])
            / (x1 - x) `} [x0] = (F [x0] - F [x]) / (x0 - x)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6. clear J6.
          rewrite H5. rewrite H5.
          assert (J6 : (f [x0] - f [a] - (f [b] - f [a])
            / (b - a) * (x0 - a) - (f [x] - f [a]
            - (f [b] - f [a]) / (b - a) * (x - a))) /
            (x0 - x) - (y' - (f [b] - f [a]) / (b - a))
            = (f [x0] - f [x]) / (x0 - x) - y').
          { field. destruct J4 as [J4 K1]. split; try lra.
            intro K2. rewrite K2 in J4.
            rewrite Abs_ge in J4; lra. }
          rewrite J6. clear J6. assumption. }
  assert (H10 : F[a] = F[b]).
  { rewrite H5; rewrite H5. field. lra. }
  generalize (Theorem6_1 F a b H0 H8 H9 H10).
  intros [ξ [H11 H12]]. exists ξ. split; auto.
  apply H2 in H11 as H13. destruct H13 as [f' H13].
  assert (H14 : derivative F ξ (f' - (f [b] - f [a]) / (b - a))).
  { split; auto. split.
    - exists 1. split; try lra. intros x0 I1.
      rewrite H3. apply AxiomII.
      exists (f[x0] - f[a] - (f[b] - f[a]) / (b - a) * (x0 - a)).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct H13 as [H13 [[δ' [I1 I2]] I3]].
      destruct I3 as [I3 [δ0' [I4 [I5 I6]]]]. split.
      + intros x1 y1 z1 J1 J2. applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + exists δ0'. repeat split; auto.
        * intros x0 J1. apply AxiomII.
          exists ((F[x0] - F[ξ]) / (x0 - ξ)).
          apply AxiomII'. reflexivity.
        * intros ε J1. apply I6 in J1 as J2.
          destruct J2 as [δ [J2 J3]].
          exists δ. split; auto.
          intros x J4. apply J3 in J4 as J5.
          assert (J6 : {` λ x y, y = (f[x] - f[ξ]) / (x - ξ) `} [x]
            = (f[x] - f[ξ]) / (x - ξ)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6 in J5. clear J6.
          assert (J6 : {` λ x y, y = (F[x] - F[ξ]) / (x - ξ) `} [x]
            = (F[x] - F[ξ]) / (x - ξ)).
          { apply f_x.
            - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6. clear J6.
          assert (J6 : (F [x] - F [ξ]) / (x - ξ) -
            (f' - (f [b] - f [a]) / (b - a))
            = (f [x] - f [ξ]) / (x - ξ) - f').
          { rewrite H5. rewrite H5. field.
            destruct J4 as [J4 K1]. apply Abs_not_eq_0 in J4.
            split; lra. }
          rewrite J6. assumption. }
  generalize (derivativeUnique F ξ 0 (f' - (f [b] - f [a]) / (b - a))
    H12 H14). intro H15.
  assert (H16 : f' = (f [b] - f [a]) / (b - a)). lra.
  rewrite <- H16. assumption.
Qed.

End A6_1.

Export A6_1.