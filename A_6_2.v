Require Export A_6_1.

Module A6_2.

(* 柯西中值定理 *)
Theorem Theorem6_6 : ∀ (f g: Fun) (a b : R), a < b
  -> ContinuousClose f a b -> ContinuousClose g a b
  -> (∀ x, a < x < b -> derivable f x)
  -> (∀ x, a < x < b -> derivable g x)
  -> (∀ x, a < x < b -> ~(f '[x] = 0 /\ g '[x] = 0))
  -> g[b] <> g[a]
  -> ∃ ξ, a < ξ < b /\
    (f '[ξ])/(g '[ξ]) = ((f[b] - f[a]) / (g[b] - g[a])).
Proof.
  intros f g a b H0 H1 H2 H3 H4 H50 H20.
  assert (H5 : (∀ x u v, a < x < b -> derivative f x u
      -> derivative g x v -> ~(u = 0 /\ v = 0))).
  { intros x u v I1 I2 I3.
    apply derEqual in I2 as I4.
    apply derEqual in I3 as I5.
    rewrite <- I4; rewrite <- I5.
    auto. }
  assert (H6 : ∃ F, F = {` λ x y, y = f[x] - f[a]
    - (f[b] - f[a])/(g[b] - g[a])*(g[x] - g[a]) `}).
  { exists {` λ x y, y = f[x] - f[a]
      - (f[b] - f[a])/(g[b] - g[a])*(g[x] - g[a]) `}.
    reflexivity. }
  destruct H6 as [F H6].
  assert (H7 : Function F).
  { rewrite H6. unfold Function. intros x y z I1 I2.
    applyAxiomII' I1. applyAxiomII' I2.
    rewrite I2. assumption. }
  assert (H8 : ∀ x, F[x] = f[x] - f[a]
    - (f[b] - f[a])/(g[b] - g[a])*(g[x] - g[a])).
  { intro x. apply f_x; auto. rewrite H6. apply AxiomII'.
    reflexivity. }
  destruct H1 as [H1 [H9 H10]].
  unfold ContinuousOpen in H1.
  destruct H2 as [H2 [H11 H12]].
  unfold ContinuousOpen in H2.
  assert (H13 : ContinuousClose F a b).
  { unfold ContinuousClose. split; [idtac | split].
    - intros x I1. unfold Continuous. split.
      + apply AxiomII. exists (f[x] - f[a]
        - (f[b] - f[a])/(g[b] - g[a])*(g[x] - g[a])).
            rewrite H6. apply AxiomII'. reflexivity.
      + unfold limit. split; auto. apply H1 in I1 as I2.
        unfold Continuous in I2. destruct I2 as [I2 I3].
        unfold limit in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(g[b] - g[a])*(g[x0] - g[a])).
          rewrite H6. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x0 : R,0 < Abs [x0 - x] < δ2 ->
            Abs[(f [b] - f [a]) / (g[b] - g[a]) * (g[x0] - g[x])] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - apply H2 in I1 as K2. destruct K2 as [K2 K3].
              destruct K3 as [K3 [δ'' [K4 [K5 K6]]]].
              assert (K7 : ε / 2 * Abs[(g[b] - g[a])/(f[b] - f[a])] > 0).
              { apply Rmult_gt_0_compat; auto.
                apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply K6 in K7 as K8.
              destruct K8 as [δ2' [K9 K10]].
              exists δ2'. split; try lra.
              intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < Abs[(f[b] - f[a])/(g[b] - g[a])]).
              { apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with
                (r := Abs[(f[b] - f[a])/(g[b] - g[a])]) in K12;
              try lra.
              assert (K14 : ε / 2 * Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])] = ε / 2 * (Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])])). field.
              rewrite K14 in K12. clear K14.
              rewrite <- Abs_mult in K12.
              rewrite <- Abs_mult in K12.
              assert (K14 : (g [b] - g [a]) / (f [b] - f [a]) *
                ((f [b] - f [a]) / (g [b] - g [a])) = 1).
              { field. split; lra. }
              rewrite K14 in K12. clear K14.
              rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g [x0] - g [x]) * ((f [b] - f [a])
                / (g [b] - g [a])) = (f [b] - f [a])
                / (g [b] - g [a]) * (g [x0] - g [x])).
              { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). repeat split; lra.
            - exists (δ2 / 2). repeat split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          assert (J11 : F[x0] - F[x] = f[x0] - f[x] -
            (f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[x])).
          { rewrite H8. rewrite H8. field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[x])
            ((f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[x]))).
          intro J11. assert (J12 : 0 < Abs[x0 - x] < δ1).
          lra. apply J4 in J12. assert (J13 : 0 < Abs[x0 - x] < δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousRight. split.
      + apply AxiomII. exists (f[a] - f[a]
        - (f[b] - f[a])/(g[b] - g[a])*(g[a] - g[a])).
            rewrite H6. apply AxiomII'. reflexivity.
      + unfold limit_pos. split; auto.
        unfold ContinuousRight in H9. destruct H9 as [I2 I3].
        unfold limit_pos in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(g[b] - g[a])*(g[x0] - g[a])).
          rewrite H6. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x : R,a < x < a + δ2 ->
            Abs[(f [b] - f [a]) / (g[b] - g[a]) * (g[x] - g[a])] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - destruct H11 as [K2 K3].
              destruct K3 as [K3 [δ'' [K4 [K5 K6]]]].
              assert (K7 : ε / 2 * Abs[(g[b] - g[a])/(f[b] - f[a])] > 0).
              { apply Rmult_gt_0_compat; auto.
                apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply K6 in K7 as K8.
              destruct K8 as [δ2' [K9 K10]].
              exists δ2'. split; try lra.
              intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < Abs[(f[b] - f[a])/(g[b] - g[a])]).
              { apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with
                (r := Abs[(f[b] - f[a])/(g[b] - g[a])]) in K12;
              try lra.
              assert (K14 : ε / 2 * Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])] = ε / 2 * (Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])])). field.
              rewrite K14 in K12. clear K14.
              rewrite <- Abs_mult in K12.
              rewrite <- Abs_mult in K12.
              assert (K14 : (g [b] - g [a]) / (f [b] - f [a]) *
                ((f [b] - f [a]) / (g [b] - g [a])) = 1).
              { field. split; lra. }
              rewrite K14 in K12. clear K14.
              rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g [x0] - g [a]) * ((f [b] - f [a])
                / (g [b] - g [a])) = (f [b] - f [a])
                / (g [b] - g [a]) * (g [x0] - g [a])).
              { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). repeat split; lra.
            - exists (δ2 / 2). repeat split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          assert (J11 : F[x0] - F[a] = f[x0] - f[a] -
            (f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[a])).
          { rewrite H8. rewrite H8. field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[a])
            ((f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[a]))).
          intro J11. assert (J12 : a < x0 < a + δ1).
          lra. apply J4 in J12. assert (J13 : a < x0 < a + δ2).
          lra. apply J6 in J13. lra.
    - unfold ContinuousLeft. split.
      + apply AxiomII. exists (f[b] - f[a]
        - (f[b] - f[a])/(g[b] - g[a])*(g[b] - g[a])).
            rewrite H6. apply AxiomII'. reflexivity.
      + unfold limit_neg. split; auto.
        unfold ContinuousLeft in H10. destruct H10 as [I2 I3].
        unfold limit_neg in I3. destruct I3 as [I3 [δ' [I4 [I5 I6]]]].
        exists δ'. split; auto. split.
        * intros x0 J1. apply AxiomII. exists (f[x0] - f[a]
          - (f[b] - f[a])/(g[b] - g[a])*(g[x0] - g[a])).
          rewrite H6. apply AxiomII'. reflexivity.
        * intros ε J1. assert (J2 : ε/2 > 0). lra.
          apply I6 in J2 as J3.
          destruct J3 as [δ1 [J3 J4]].
          assert (J5 : ∃ δ2, 0 < δ2 /\ ∀ x : R,b - δ2 < x < b ->
            Abs[(f [b] - f [a]) / (g[b] - g[a]) * (g[x] - g[b])] < ε/2).
          { destruct classic with (P := (f [b] - f [a] = 0)) as [K1 | K1].
            - exists 1. split; try lra. intros x0 K2.
              rewrite K1. unfold Rdiv. rewrite Rmult_0_l. rewrite Rmult_0_l.
              rewrite Abs_ge; try lra.
            - destruct H12 as [K2 K3].
              destruct K3 as [K3 [δ'' [K4 [K5 K6]]]].
              assert (K7 : ε / 2 * Abs[(g[b] - g[a])/(f[b] - f[a])] > 0).
              { apply Rmult_gt_0_compat; auto.
                apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply K6 in K7 as K8.
              destruct K8 as [δ2' [K9 K10]].
              exists δ2'. split; try lra.
              intros x0 K11. apply K10 in K11 as K12.
              assert (K13 : 0 < Abs[(f[b] - f[a])/(g[b] - g[a])]).
              { apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified;
                try lra. apply Rinv_neq_0_compat. lra. }
              apply Rmult_lt_compat_r with
                (r := Abs[(f[b] - f[a])/(g[b] - g[a])]) in K12;
              try lra.
              assert (K14 : ε / 2 * Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])] = ε / 2 * (Abs [(g [b] - g [a])
                / (f [b] - f [a])] * Abs [(f [b] - f [a])
                / (g [b] - g [a])])). field.
              rewrite K14 in K12. clear K14.
              rewrite <- Abs_mult in K12.
              rewrite <- Abs_mult in K12.
              assert (K14 : (g [b] - g [a]) / (f [b] - f [a]) *
                ((f [b] - f [a]) / (g [b] - g [a])) = 1).
              { field. split; lra. }
              rewrite K14 in K12. clear K14.
              rewrite (Abs_ge 1) in K12; try lra.
              rewrite Rmult_1_r in K12.
              assert (K14 : (g [x0] - g [b]) * ((f [b] - f [a])
                / (g [b] - g [a])) = (f [b] - f [a])
                / (g [b] - g [a]) * (g [x0] - g [b])).
              { field. lra. }
              rewrite K14 in K12. assumption. }
          destruct J5 as [δ2 [J5 J6]].
          assert (J7 : ∃ δ, δ > 0 /\ δ < δ1 /\ δ < δ2).
          { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
            - exists (δ1 / 2). repeat split; lra.
            - exists (δ2 / 2). repeat split; lra. }
          destruct J7 as [δ [J7 [J8 J9]]].
          exists δ. split; try lra. intros x0 J10.
          assert (J11 : F[x0] - F[b] = f[x0] - f[b] -
            (f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[b])).
          { rewrite H8. rewrite H8. field. lra. }
          rewrite J11. clear J11.
          generalize (Abs_minus_le (f[x0] - f[b])
            ((f[b] - f[a]) / (g[b] - g[a]) * (g[x0] - g[b]))).
          intro J11. assert (J12 : b - δ1 < x0 < b).
          lra. apply J4 in J12. assert (J13 : b - δ2 < x0 < b).
          lra. apply J6 in J13. lra. }
  assert (H14 : ∀ x, a < x < b -> derivable F x).
  { intros x I1. apply H3 in I1 as I2. apply H4 in I1 as I20.
    destruct I2 as [y1' [I2 [[δ1' [I3 I4]] I5]]].
    destruct I20 as [y2' [I21 [[δ2' [I22 I23]] I24]]].
    exists (y1' - (f[b] - f[a]) / (g[b] - g[a]) * y2').
    split; auto. split.
    - exists δ1'. split; auto. intros x0 J1.
      apply AxiomII. rewrite H6.
      exists (f[x0] - f[a] - (f[b] - f[a])
      / (g[b] - g[a]) * (g[x0] - g[a])).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct I5 as [I5 [δ0' [I6 [I7 I8]]]].
      destruct I24 as [I24 [δ3' [I25 [I26 I27]]]].
      split.
      + unfold Function. intros x0 y0 z0 J1 J2.
        applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + exists δ0'. split; auto. split.
        * intros x0 J1. apply AxiomII.
          exists ((F [x0] - F [x]) / (x0 - x)).
          apply AxiomII'. reflexivity.
        * intros ε J1. assert (J20 : ε/2 > 0). lra.
          apply I8 in J20 as J2.
          destruct J2 as [δ1 [J2 J3]].
          destruct classic with (P := (f [b] - f [a] = 0)) as [L1 | L1].
          -- exists δ1. split; try lra.
            intros x0 J4.
            assert (J6 : {` λ x1 y, y = (F [x1] - F [x])
              / (x1 - x) `} [x0] = (F [x0] - F [x]) / (x0 - x)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
                applyAxiomII' K1; applyAxiomII' K2.
                rewrite K2. assumption.
              - apply AxiomII'. reflexivity. }
            rewrite J6. clear J6.
            rewrite H8; rewrite H8.
            rewrite L1 in *. unfold Rdiv. rewrite Rmult_0_l in *.
            rewrite Rmult_0_l in *. rewrite Rmult_0_l in *.
            rewrite Rmult_0_l in *.
            assert (J5 : (f[x0] - f[a] - 0 - (f[x] - f[a] - 0))
              * / (x0 - x) - (y1' - 0) =
              (f[x0] - f[x]) / (x0 - x) - y1').
            { field. destruct J4 as [J4 J5].
              apply Abs_not_eq_0 in J4. assumption. }
            rewrite J5. clear J5. apply J3 in J4.
            assert (J6 : {` λ x0 y, y =
              (f [x0] - f [x]) / (x0 - x) `} [x0]
              = (f [x0] - f [x]) / (x0 - x)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
                applyAxiomII' K1; applyAxiomII' K2.
                rewrite K2. assumption.
              - apply AxiomII'. reflexivity. }
            rewrite J6 in J4. lra.
          -- assert (J30 : Abs[(g[b] - g[a]) / (f[b] - f[a])]
              * (ε / 2) > 0).
            { apply Rmult_gt_0_compat; try lra.
              apply Abs_not_eq_0.
              apply Rmult_integral_contrapositive_currified; try lra.
              apply Rinv_neq_0_compat. lra. }
            apply I27 in J30 as J21.
            destruct J21 as [δ2 [J21 J22]].
            assert (J25 : ∃ δ, 0 < δ /\ δ < δ1 /\ δ < δ2).
            { destruct (Rlt_or_le δ1 δ2) as [K1 | K1].
              - exists (δ1 / 2). repeat split; lra.
              - exists (δ2 / 2). repeat split; lra. }
            destruct J25 as [δ [J26 [J23 J24]]].
            exists δ. split; try lra.
            intros x0 J4.
            assert (J27 : 0 < Abs[x0 - x] < δ1). lra.
            assert (J28 : 0 < Abs[x0 - x] < δ2). lra.
            apply J3 in J27 as J5.
            apply J22 in J28 as J29.
            assert (J6 : {` λ x0 y, y =
              (f [x0] - f [x]) / (x0 - x) `} [x0]
              = (f [x0] - f [x]) / (x0 - x)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
                applyAxiomII' K1; applyAxiomII' K2.
                rewrite K2. assumption.
              - apply AxiomII'. reflexivity. }
            rewrite J6 in J5. clear J6.
            assert (J6 : {` λ x0 y, y =
              (g [x0] - g [x]) / (x0 - x) `} [x0]
              = (g [x0] - g [x]) / (x0 - x)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
                applyAxiomII' K1; applyAxiomII' K2.
                rewrite K2. assumption.
              - apply AxiomII'. reflexivity. }
            rewrite J6 in J29. clear J6.
            assert (J6 : {` λ x1 y, y = (F [x1] - F [x])
              / (x1 - x) `} [x0] = (F [x0] - F [x]) / (x0 - x)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
              applyAxiomII' K1; applyAxiomII' K2.
              rewrite K2. assumption.
            - apply AxiomII'. reflexivity. }
          rewrite J6. clear J6.
          rewrite H8; rewrite H8.
          assert (J6 : (f [x0] - f [a] - (f [b] - f [a])
            / (g [b] - g [a]) * (g [x0] - g [a]) -
            (f [x] - f [a] - (f [b] - f [a])
            / (g [b] - g [a]) * (g [x] - g [a]))) / 
            (x0 - x) - (y1' - (f [b] - f [a]) / (g [b] - g [a]) * y2')
            = (f[x0] - f[x]) / (x0 - x) - y1' -
            ((f[b] - f[a]) / (g[b] - g[a])
            * ((g[x0] - g[x]) / (x0 - x) - y2'))).
          { field. destruct J4 as [J4 K1].
            apply Abs_not_eq_0 in J4. split; lra. }
          rewrite J6. clear J6.
          generalize (Abs_minus_le 
            ((f[x0] - f[x]) / (x0 - x) - y1')
            ((f [b] - f [a]) / (g [b] - g [a]) *
            ((g [x0] - g [x]) / (x0 - x) - y2'))).
          intro J6. assert (J7 : 0 < Abs [(f [b] - f [a]) / (g [b] - g [a])]).
          { apply Abs_not_eq_0.
            apply Rmult_integral_contrapositive_currified; auto.
            apply Rinv_neq_0_compat. lra. }
          apply Rmult_lt_compat_l with
            (r := Abs [(f[b] - f[a]) / (g[b] - g[a])]) in J29; auto.
          rewrite <- Abs_mult in J29. rewrite <- Rmult_assoc in J29.
          rewrite <- Abs_mult in J29.
          assert (J31 : (f [b] - f [a]) / (g [b] - g [a]) *
            ((g [b] - g [a]) / (f [b] - f [a])) = 1).
          { field. split; lra. }
          rewrite J31 in J29.
          assert (J32 : Abs [1] * (ε / 2) = ε / 2).
          { rewrite Abs_gt; try lra. }
          rewrite J32 in J29. lra. }
  assert(H15 : F[a] = F[b]).
  { rewrite H8; rewrite H8. field. lra. }
  generalize (Theorem6_1 F a b H0 H13 H14 H15).
  intros [ξ [H16 H17]]. exists ξ. apply H3 in H16 as H18.
  unfold derivable in H18. destruct H18 as [s H18].
  apply H4 in H16 as H19. destruct H19 as [t H19].
  split; auto.
  assert (H21 : derivative F ξ (s - (f[b] - f[a]) / (g[b] - g[a]) * t)).
  { split; auto. split.
    - exists 1. split; try lra. intros x0 I1.
      rewrite H6. apply AxiomII.
      exists (f[x0] - f[a] - (f[b] - f[a])
      / (g[b] - g[a]) * (g[x0] - g[a])).
      apply AxiomII'. reflexivity.
    - unfold limit. destruct H18 as [H18 [[δ1' [I1 I2]] I3]].
      destruct I3 as [I3 [δ0' [I4 [I5 I6]]]].
      destruct H19 as [H19 [[δ2' [I11 I12]] I13]].
      destruct I13 as [I13 [δ3' [I14 [I15 I16]]]].
      split.
      + intros x1 y1 z1 J1 J2. applyAxiomII' J1; applyAxiomII' J2.
        rewrite J2. assumption.
      + assert (I7 : ∃ δ4', δ4' > 0 /\ δ4' < δ0' /\ δ4' < δ3').
        { destruct (Rlt_or_le δ0' δ3') as [J1 | J1].
          - exists (δ0'/2). repeat split; lra.
          - exists (δ3'/2). repeat split; lra. }
        destruct I7 as [δ4' [I7 [I8 I9]]].
        exists δ4'. repeat split; auto.
        * intros x0 J1. apply AxiomII.
          exists ((F[x0] - F[ξ]) / (x0 - ξ)).
          apply AxiomII'. reflexivity.
        * intros ε J1. assert (J7 : ε/2 > 0). lra.
          apply I6 in J7 as J2.
          destruct J2 as [δ0 [J2 J3]].
          assert (J9 : ∃ δ1, δ1 > 0 /\ δ1 < δ0 /\ δ1 < δ4').
          { destruct (Rlt_or_le δ0 δ4') as [K1 | K1].
            - exists (δ0/2). repeat split; lra.
            - exists (δ4'/2). repeat split; lra. }
          destruct J9 as [δ1 [J10 [J11 J12]]].
          destruct classic with (P := (f [b] - f [a] = 0)) as [J8 | J8].
          -- exists δ1. split; try lra. intros x K1.
            assert (K2 : {` λ x0 y : R,y =
              (F[x0] - F[ξ]) / (x0 - ξ) `} [x] =
              (F[x] - F[ξ]) / (x - ξ)).
            { apply f_x.
              - intros x1 y1 z1 L1 L2. applyAxiomII' L1.
                applyAxiomII' L2. rewrite L2; assumption.
              - apply AxiomII'. reflexivity. }
            rewrite K2.
            assert (K3 : F[x] - F[ξ] = f[x] - f[ξ]).
            { rewrite H8; rewrite H8. rewrite J8.
              field. lra. }
            rewrite K3.
            assert (K4 : s - (f [b] - f [a])
              / (g [b] - g [a]) * t = s).
            { rewrite J8. field. lra. }
            rewrite K4. assert (K5 : 0 < Abs[x - ξ] < δ0). lra.
            apply J3 in K5.
            assert (K6 : {` λ x y : R,y =
              (f[x] - f[ξ]) / (x - ξ) `} [x] =
              (f[x] - f[ξ]) / (x - ξ)).
            { apply f_x.
              - intros x1 y1 z1 L1 L2. applyAxiomII' L1.
                applyAxiomII' L2. rewrite L2; assumption.
              - apply AxiomII'. reflexivity. }
            rewrite K6 in K5. lra.
          -- assert (J13 : ε/2 * Abs[(g[b] - g[a])/(f[b] - f[a])] > 0).
            { apply Rmult_gt_0_compat; auto.
              apply Abs_not_eq_0.
              apply Rmult_integral_contrapositive_currified; try lra.
              apply Rinv_neq_0_compat. assumption. }
            apply I16 in J13 as J14.
            destruct J14 as [δ2 [J14 J15]].
            assert (J9 : ∃ δ, δ > 0 /\ δ < δ0 /\ δ < δ4' /\ δ < δ2).
            { destruct (Rlt_or_le δ0 δ4') as [K1 | K1].
              - destruct (Rlt_or_le δ0 δ2) as [K2 | K2].
                + exists (δ0/2). repeat split; lra.
                + exists (δ2/2). repeat split; lra.
              - destruct (Rlt_or_le δ4' δ2) as [K2 | K2].
                + exists (δ4'/2). repeat split; lra.
                + exists (δ2/2). repeat split; lra. }
            destruct J9 as [δ [J9 [J16 [J17 J18]]]].
            exists δ. split; auto.
            intros x J4.
            assert (J5 : 0 < Abs[x - ξ] < δ0). lra.
            apply J3 in J5.
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
            assert (J19 : 0 < Abs [x - ξ] < δ2). lra.
            apply J15 in J19.
            assert (J6 : {` λ x y, y = (g[x] - g[ξ]) / (x - ξ) `} [x]
              = (g[x] - g[ξ]) / (x - ξ)).
            { apply f_x.
              - intros x1 y1 z1 K1 K2.
                applyAxiomII' K1; applyAxiomII' K2.
                rewrite K2. assumption.
              - apply AxiomII'. reflexivity. }
            rewrite J6 in J19. clear J6.
            assert (J6 : (F[x] - F[ξ]) / (x - ξ) -
             (s - (f[b] - f[a]) / (g[b] - g[a]) * t) =
             (f[x] - f[ξ])/(x - ξ) - s -
             (f[b] - f[a]) / (g[b] - g[a])
             * ((g[x] - g[ξ])/(x - ξ) - t)).
            { rewrite H8. rewrite H8. field.
              destruct J4 as [J4 K1]. apply Abs_not_eq_0 in J4.
              split; lra. }
            rewrite J6. clear J6.
            generalize (Abs_minus_le ((f[x] - f[ξ])/(x - ξ) - s)
              ((f[b] - f[a]) / (g[b] - g[a])
             * ((g[x] - g[ξ])/(x - ξ) - t))).
            intro J20.
            assert (J21 : Abs[(f[b] - f[a]) / (g[b] - g[a])
             * ((g[x] - g[ξ])/(x - ξ) - t)] < ε / 2).
            { rewrite Abs_mult.
              assert (K1 : 0 < Abs[(g[b] - g[a]) / (f[b] - f[a])]).
              { apply Abs_not_eq_0.
                apply Rmult_integral_contrapositive_currified.
                lra. apply Rinv_neq_0_compat. assumption. }
              apply Rmult_lt_reg_r with (r :=
                Abs [(g[b] - g[a]) / (f[b] - f[a])]); auto.
              assert (K2 : Abs[(f[b] - f[a]) / (g[b] - g[a])] *
                Abs[(g[x] - g[ξ]) / (x - ξ) - t] *
                Abs[(g[b] - g[a]) / (f[b] - f[a])] =
                Abs[(g[x] - g[ξ]) / (x - ξ) - t]).
              { rewrite (Rmult_comm (Abs[(f[b] - f[a])/ (g[b] - g[a])])
                 (Abs[(g[x] - g[ξ]) / (x - ξ) - t])).
                rewrite Rmult_assoc. rewrite <- Abs_mult.
                assert (L1 : (f[b] - f[a]) / (g[b] - g[a]) *
                  ((g[b] - g[a]) / (f[b] - f[a])) = 1).
                { field. split; lra. }
                rewrite L1.  rewrite (Abs_ge 1); lra. }
              rewrite K2. clear K2. assumption. }
            lra. }
  assert (H22 : s - (f[b] - f[a]) / (g[b] - g[a]) * t = 0).
  { eapply derivativeUnique; eauto. }
  assert (H23 : s = (f[b] - f[a]) / (g[b] - g[a]) * t). lra.
  assert (H24 : t <> 0).
  { intro I1. assert (I2 : s = 0).
    { rewrite I1 in H23. rewrite Rmult_0_r in H23. assumption. }
    eapply H5; eauto. }
  apply Rmult_eq_compat_r with (r := /t) in H23.
  assert (H25 : (f[b] - f[a]) / (g[b] - g[a]) * t * / t
    = (f[b] - f[a]) / (g[b] - g[a])). field; lra.
  rewrite H25 in H23.
  apply derEqual in H18. apply derEqual in H19.
  rewrite H18. rewrite H19. assumption.
Qed.

(* 洛必达法则 *)
Theorem Theorem6_7 : ∀ (f g: Fun) (x0 A : R),
  limit f x0 0 -> limit g x0 0 ->
  (∃ δ', δ' > 0 /\ (∀ x, x ∈ Neighbor0 x0 δ' ->
    derivable f x /\ derivable g x /\ g '[x] <> 0)) ->
  limit {` λ x y, y = f '[x] / g '[x] `} x0 A ->
  limit {` λ x y, y = f[x]/g[x] `} x0 A.
Proof.
  intros f g x0 A H0 H1 [δ' [H2 H3]] H4.
  assert (H5 : ∃ f1, f1 = {` λ x y,
    (x <> x0 /\ y = f[x]) \/ (x = x0 /\ y = 0) `}).
  { exists {` λ x y, (x <> x0 /\ y = f[x])
      \/ (x = x0 /\ y = 0) `}. reflexivity. }
  destruct H5 as [f1 H5].
  assert (H6 : ∃ g1, g1 = {` λ x y,
    (x <> x0 /\ y = g[x]) \/ (x = x0 /\ y = 0) `}).
  { exists {` λ x y, (x <> x0 /\ y = g[x])
      \/ (x = x0 /\ y = 0) `}. reflexivity. }
  destruct H6 as [g1 H6].
  assert (H8 : Neighbor0 x0 δ' ⊂ dom[f]).
  { intros x I1. apply H3 in I1 as I2.
    destruct I2 as [I2 I3].
    destruct I2 as [y0' I2].
    unfold derivative in I2.
    destruct I2 as [I2 [[δ0' [I6 I4]] I5]].
    apply I4. apply AxiomII. unfold Rminus.
    rewrite Rplus_opp_r.
    assert (I7 : Abs[0] = 0).
    { apply Abs_ge. lra. }
    rewrite I7. assumption. }
  assert (H9 : Function f1).
  { intros x y z I1 I2. rewrite H5 in *.
    applyAxiomII' I1; applyAxiomII' I2.
    destruct I1 as [[I1 I3] | [I1 I3]].
    - destruct I2 as [[I2 I4] | [I2 I4]];
      [lra | contradiction].
    - destruct I2 as [[I2 I4] | [I2 I4]];
      [contradiction | lra]. }
  assert (H10 : Function g1).
  { intros x y z I1 I2. rewrite H6 in *.
    applyAxiomII' I1; applyAxiomII' I2.
    destruct I1 as [[I1 I3] | [I1 I3]].
    - destruct I2 as [[I2 I4] | [I2 I4]];
      [lra | contradiction].
    - destruct I2 as [[I2 I4] | [I2 I4]];
      [contradiction | lra]. }
  assert (H11 : ∀ x, x <> x0 -> f[x] = f1[x]).
  { intros x I1. symmetry. apply f_x; auto.
    rewrite H5. apply AxiomII'.
    left. split; auto. }
  assert (H12 : ∀ x, x <> x0 -> g[x] = g1[x]).
  { intros x I1. symmetry. apply f_x; auto.
    rewrite H6. apply AxiomII'.
    left. split; auto. }
  assert (H13 : f1[x0] = 0).
  { apply f_x; auto. rewrite H5.
    apply AxiomII'. right. split; auto. }
  assert (H14 : g1[x0] = 0).
  { apply f_x; auto. rewrite H6.
    apply AxiomII'. right. split; auto. }
  assert (H15 : ∀ x, x ∈ Neighbor0 x0 δ'
    -> derivative f1 x (f '[x]) /\
    derivative g1 x (g '[x])).
  { intros x I1. apply H3 in I1 as I2.
    destruct I2 as [[y1' I2] [[y2' I3] I4]].
    apply derEqual in I2 as I11.
    apply derEqual in I3 as I12.
    destruct I2 as [I2 [[δ1' [I5 I6]] I7]].
    destruct I3 as [I3 [[δ2' [I8 I9]] I10]].
    rewrite I11. rewrite I12.
    applyAxiomII I1. destruct I1 as [I1 I13].
    apply Abs_not_eq_0 in I1 as I14.
    assert (I15 : Function {` λ x1 y,
      y = (f[x1] - f[x]) / (x1 - x) `}).
    { intros x1 y1 z1 K1 K2.
      applyAxiomII' K1; applyAxiomII' K2.
      rewrite K2; assumption. }
    assert (I16 : Function {` λ x1 y,
      y = (f1[x1] - f1[x]) / (x1 - x) `}).
    { intros x1 y1 z1 K1 K2.
      applyAxiomII' K1; applyAxiomII' K2.
      rewrite K2; assumption. }
    assert (I17 : Function {` λ x1 y,
      y = (g[x1] - g[x]) / (x1 - x) `}).
    { intros x1 y1 z1 K1 K2.
      applyAxiomII' K1; applyAxiomII' K2.
      rewrite K2; assumption. }
    assert (I18 : Function {` λ x1 y,
      y = (g1[x1] - g1[x]) / (x1 - x) `}).
    { intros x1 y1 z1 K1 K2.
      applyAxiomII' K1; applyAxiomII' K2.
      rewrite K2; assumption. }
    split.
    - split; auto. split.
      + exists δ1'. split; auto.
        intros x1 J1. apply AxiomII.
        destruct classic with (P := x1 = x0) as [J2 | J2].
        * exists 0. rewrite H5. apply AxiomII'.
          right; split; auto.
        * exists f[x1]. rewrite H5. apply AxiomII'.
          left; split; auto.
      + unfold limit.
        split; auto.
        destruct I7 as [I7 [δ0' [J2 [J3 J4]]]].
        exists δ0'. split; auto. split.
        * intros x1 K1. apply AxiomII.
          exists ((f1[x1] - f1[x])/(x1 - x)).
          apply AxiomII'. reflexivity.
        * intros ε K1. apply J4 in K1 as K2.
          destruct K2 as [δ1 [[K2 K3] K4]].
          generalize (Lemma1 δ1 Abs[x - x0] K2 I1).
          intros [δ [K5 [K6 K7]]].
          exists δ. split; try lra.
          intros x1 K8.
          assert (K9 : {` λ x2 y,
            y = (f1[x2] - f1[x])/(x2 - x) `} [x1]
            = (f1[x1] - f1[x])/(x1 - x)).
          { apply f_x; auto. apply AxiomII'.
            reflexivity. }
          rewrite K9.
          assert (K10 : 0 < Abs [x1 - x] < δ1). lra.
          apply K4 in K10 as K11.
          assert (K12 : {` λ x0 y,
            y = (f[x0] - f[x])/(x0 - x) `} [x1]
            = (f[x1] - f[x])/(x1 - x)).
          { apply f_x; auto. apply AxiomII'.
            reflexivity. }
          rewrite K12 in K11. clear K12.
          assert (K12 : x1 <> x0).
          { intros L1. rewrite L1 in K8.
            rewrite Abs_eq_neg in K7.
            rewrite Ropp_minus_distr in K7.
            lra. }
          rewrite <- H11; auto. rewrite <- H11; auto.
          lra.
    - split; auto. split.
      + exists δ2'. split; auto.
        intros x1 J1. apply AxiomII.
        destruct classic with (P := x1 = x0) as [J2 | J2].
        * exists 0. rewrite H6. apply AxiomII'.
          right; split; auto.
        * exists g[x1]. rewrite H6. apply AxiomII'.
          left; split; auto.
      + unfold limit.
        split; auto.
        destruct I10 as [I10 [δ0' [J2 [J3 J4]]]].
        exists δ0'. split; auto. split.
        * intros x1 K1. apply AxiomII.
          exists ((g1[x1] - g1[x])/(x1 - x)).
          apply AxiomII'. reflexivity.
        * intros ε K1. apply J4 in K1 as K2.
          destruct K2 as [δ1 [[K2 K3] K4]].
          generalize (Lemma1 δ1 Abs[x - x0] K2 I1).
          intros [δ [K5 [K6 K7]]].
          exists δ. split; try lra.
          intros x1 K8.
          assert (K9 : {` λ x2 y,
            y = (g1[x2] - g1[x])/(x2 - x) `} [x1]
            = (g1[x1] - g1[x])/(x1 - x)).
          { apply f_x; auto. apply AxiomII'.
            reflexivity. }
          rewrite K9.
          assert (K10 : 0 < Abs [x1 - x] < δ1). lra.
          apply K4 in K10 as K11.
          assert (K12 : {` λ x0 y,
            y = (g[x0] - g[x])/(x0 - x) `} [x1]
            = (g[x1] - g[x])/(x1 - x)).
          { apply f_x; auto. apply AxiomII'.
            reflexivity. }
          rewrite K12 in K11. clear K12.
          assert (K12 : x1 <> x0).
          { intros L1. rewrite L1 in K8.
            rewrite Abs_eq_neg in K7.
            rewrite Ropp_minus_distr in K7.
            lra. }
          rewrite <- H12; auto. rewrite <- H12; auto.
          lra. }
  assert (H16 : ∀ x, x ∈ Neighbor0 x0 δ' ->
    Continuous f1 x /\ Continuous g1 x).
  { intros x I1. apply H15 in I1 as [I1 I2].
    split; apply Theorem5_1; auto;
    [exists (f '[ x]) | exists (g '[ x])]; auto. }
  assert (H17 : limit f1 x0 0).
  { destruct H0 as [H0 [δ0' [I2 [I3 I4]]]].
    split; auto. exists δ0'. split; auto.
    split.
    - intros x1 J1. applyAxiomII J1.
      apply AxiomII. exists f[x1].
      rewrite H5. apply AxiomII'.
      left. apply Lemma2 in J1.
      split; lra.
    - intros ε I5.
      apply I4 in I5 as I6.
      destruct I6 as [δ [I6 I7]].
      exists δ. split; auto.
      intros x1 I8.
      apply Lemma2 in I8 as I10.
      assert (I9 : x1 <> x0). lra.
      rewrite <- H11; auto. }
  assert (H18 : limit g1 x0 0).
  { destruct H1 as [H1 [δ0' [I2 [I3 I4]]]].
    split; auto. exists δ0'. split; auto.
    split.
    - intros x1 J1. applyAxiomII J1.
      apply AxiomII. exists g[x1].
      rewrite H6. apply AxiomII'.
      left. apply Lemma2 in J1.
      split; lra.
    - intros ε I5.
      apply I4 in I5 as I6.
      destruct I6 as [δ [I6 I7]].
      exists δ. split; auto.
      intros x1 I8.
      apply Lemma2 in I8 as I10.
      assert (I9 : x1 <> x0). lra.
      rewrite <- H12; auto. }
  assert (H19 : ∀ x, x ∈ Neighbor0 x0 δ' -> g1[x] <> 0).
  { intros x I1 I2. apply H16 in I1 as I5.
    destruct I5 as [I5 I6].
    applyAxiomII I1.
    destruct I1 as [I3 I4].
    apply Abs_R in I4. apply Abs_not_eq_0 in I3.
    apply Rdichotomy in I3 as [I3 | I3].
    - assert (J1 : ContinuousClose g1 x x0).
      { split; [idtac | split].
        - intros x1 K1.
          assert (K2 : x1 ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in K2 as [K2 K3].
          assumption.
        - destruct I6 as [I6 I7]. split; auto.
          apply Theorem3_1. assumption.
        - split.
          + apply AxiomII. exists 0. rewrite H6.
            apply AxiomII'. right. split; reflexivity.
          + apply Theorem3_1. rewrite H14. assumption. }
      assert (J2 : ∀ x1, x < x1 < x0 -> derivable g1 x1).
      { intros x1 K1. exists (g '[x1]).
        apply H15. apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      assert (J3 : g1[x] = g1[x0]). lra.
      assert (J4 : x < x0). lra.
      generalize (Theorem6_1 g1 x x0 J4 J1 J2 J3).
      intros [ξ [J5 J6]].
      assert (J7 : ξ ∈ Neighbor0 x0 δ').
      { apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      apply H3 in J7 as J8.
      destruct J8 as [J8 [J9 J10]].
      apply J10. apply H15 in J7 as [J11 J12].
      eapply derivativeUnique; eauto.
    - assert (J1 : ContinuousClose g1 x0 x).
      { split; [idtac | split].
        - intros x1 K1.
          assert (K2 : x1 ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in K2 as [K2 K3].
          assumption.
        - split.
          + apply AxiomII. exists 0. rewrite H6.
            apply AxiomII'. right. split; reflexivity.
          + apply Theorem3_1. rewrite H14. assumption.
        - destruct I6 as [I6 I7]. split; auto.
          apply Theorem3_1. assumption. }
      assert (J2 : ∀ x1, x0 < x1 < x -> derivable g1 x1).
      { intros x1 K1. exists (g '[x1]).
        apply H15. apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      assert (J3 : g1[x0] = g1[x]). lra.
      assert (J4 : x0 < x). lra.
      generalize (Theorem6_1 g1 x0 x J4 J1 J2 J3).
      intros [ξ [J5 J6]].
      assert (J7 : ξ ∈ Neighbor0 x0 δ').
      { apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      apply H3 in J7 as J8.
      destruct J8 as [J8 [J9 J10]].
      apply J10. apply H15 in J7 as [J11 J12].
      eapply derivativeUnique; eauto. }
  assert (H20 : ∀ x, x0 < x < x0 + δ' ->
    ∃ ξ, x0 < ξ < x /\ f[x]/g[x] = f '[ξ] / g '[ξ]).
  { intros x I1.
    assert (I2 : ContinuousClose f1 x0 x).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Neighbor0 x0 δ').
        { apply AxiomII.
          assert (K1 : x1 - x0 > 0). lra.
          rewrite Abs_gt; auto. split; lra. }
        apply H16 in J2 as [J2 J3].
        assumption.
      - destruct H0 as [H0 [δ0' [I2 [I3 I4]]]].
        split.
        + apply AxiomII.
          exists 0. rewrite H5.
          apply AxiomII'. right. split; reflexivity.
        + rewrite H13. apply Theorem3_1. assumption.
      - split.
        + apply AxiomII. exists f[x].
          rewrite H5. apply AxiomII'.
          left; split; lra.
        + assert (I2 : x ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in I2 as I3.
          destruct I3 as [I3 I4].
          destruct I3 as [I3 I5].
          apply Theorem3_1. assumption. }
    assert (I3 : ContinuousClose g1 x0 x).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Neighbor0 x0 δ').
        { apply AxiomII.
          assert (K1 : x1 - x0 > 0). lra.
          rewrite Abs_gt; auto. split; lra. }
        apply H16 in J2 as [J2 J3].
        assumption.
      - destruct H1 as [H1 [δ0' [I10 [I3 I4]]]].
        split.
        + apply AxiomII.
          exists 0. rewrite H6.
          apply AxiomII'. right. split; reflexivity.
        + rewrite H14. apply Theorem3_1. assumption.
      - split.
        + apply AxiomII. exists g[x].
          rewrite H6. apply AxiomII'.
          left; split; lra.
        + assert (I10 : x ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in I10 as I3.
          destruct I3 as [I3 I4].
          destruct I4 as [I4 I5].
          apply Theorem3_1. assumption. }
    assert (I4 : ∀ x1, x0 < x1 < x -> derivable f1 x1).
    { intros x1 J1. exists (f '[x1]).
      apply H15. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I5 : ∀ x1, x0 < x1 < x -> derivable g1 x1).
    { intros x1 J1. exists (g '[x1]).
      apply H15. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I6 : ∀ x1, x0 < x1 < x
      -> ~(f1 '[x1] = 0 /\ g1 '[x1] = 0)).
    { intros x1 J1 [J2 J3].
      assert (J4 : x1 ∈ Neighbor0 x0 δ').
      { apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      apply H15 in J4 as J8.
      destruct J8 as [J8 J9].
      apply H3 in J4 as [J5 [J6 J7]].
      apply J7. apply derEqual in J9.
      rewrite J9 in J3. assumption. }
    assert (I7 : g1[x] <> g1[x0]).
    { rewrite H14. apply H19. apply AxiomII.
      split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    destruct I1 as [I1 I8].
    generalize (Theorem6_6 f1 g1 x0 x I1
      I2 I3 I4 I5 I6 I7).
    intros [ξ [I9 I10]].
    exists ξ. split; auto.
    rewrite H13 in I10. rewrite H14 in I10.
    assert (I11 : x <> x0). lra.
    apply H12 in I11 as I13. apply H11 in I11 as I12.
    rewrite I12; rewrite I13.
    assert (I14 : ξ ∈ Neighbor0 x0 δ').
    { apply AxiomII.
      split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    apply H15 in I14 as I15.
    destruct I15 as [I15 I16].
    apply derEqual in I15; apply derEqual in I16.
    rewrite <- I15; rewrite <- I16.
    rewrite Rminus_0_r in I10.
    rewrite Rminus_0_r in I10.
    symmetry. assumption. }
  assert (H21 : ∀ x, x0 - δ' < x < x0  ->
    ∃ ξ, x < ξ < x0 /\ f[x]/g[x] = f '[ξ] / g '[ξ]).
  { intros x I1.
    assert (I2 : ContinuousClose f1 x x0).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Neighbor0 x0 δ').
        { apply AxiomII.
          assert (K1 : x1 - x0 < 0). lra.
          rewrite Abs_lt; auto. split; lra. }
        apply H16 in J2 as [J2 J3].
        assumption.
      - split.
        + apply AxiomII. exists f[x].
          rewrite H5. apply AxiomII'.
          left; split; lra.
        + assert (I2 : x ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in I2 as I3.
          destruct I3 as [I3 I4].
          destruct I3 as [I3 I5].
          apply Theorem3_1. assumption.
      - destruct H0 as [H0 [δ0' [I2 [I3 I4]]]].
        split.
        + apply AxiomII.
          exists 0. rewrite H5.
          apply AxiomII'. right. split; reflexivity.
        + rewrite H13. apply Theorem3_1. assumption. }
    assert (I3 : ContinuousClose g1 x x0).
    { split; [idtac | split].
      - intros x1 J1.
        assert (J2 : x1 ∈ Neighbor0 x0 δ').
        { apply AxiomII.
          assert (K1 : x1 - x0 < 0). lra.
          rewrite Abs_lt; auto. split; lra. }
        apply H16 in J2 as [J2 J3].
        assumption.
      - split.
        + apply AxiomII. exists g[x].
          rewrite H6. apply AxiomII'.
          left; split; lra.
        + assert (I10 : x ∈ Neighbor0 x0 δ').
          { apply AxiomII. split.
            - apply Abs_not_eq_0. lra.
            - apply Abs_R. lra. }
          apply H16 in I10 as I3.
          destruct I3 as [I3 I4].
          destruct I4 as [I4 I5].
          apply Theorem3_1. assumption.
      - destruct H1 as [H1 [δ0' [I10 [I3 I4]]]].
        split.
        + apply AxiomII.
          exists 0. rewrite H6.
          apply AxiomII'. right. split; reflexivity.
        + rewrite H14. apply Theorem3_1. assumption. }
    assert (I4 : ∀ x1, x < x1 < x0 -> derivable f1 x1).
    { intros x1 J1. exists (f '[x1]).
      apply H15. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I5 : ∀ x1, x < x1 < x0 -> derivable g1 x1).
    { intros x1 J1. exists (g '[x1]).
      apply H15. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    assert (I6 : ∀ x1, x < x1 < x0
      -> ~(f1 '[x1] = 0 /\ g1 '[x1] = 0)).
    { intros x1 J1 [J2 J3].
      assert (J4 : x1 ∈ Neighbor0 x0 δ').
      { apply AxiomII. split.
        - apply Abs_not_eq_0. lra.
        - apply Abs_R. lra. }
      apply H15 in J4 as J8.
      destruct J8 as [J8 J9].
      apply H3 in J4 as [J5 [J6 J7]].
      apply J7. apply derEqual in J9.
      rewrite J9 in J3. assumption. }
    assert (I7 : g1[x0] <> g1[x]).
    { rewrite H14. apply not_eq_sym.
      apply H19. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    destruct I1 as [I1 I8].
    generalize (Theorem6_6 f1 g1 x x0 I8
      I2 I3 I4 I5 I6 I7).
    intros [ξ [I9 I10]].
    exists ξ. split; auto.
    rewrite H13 in I10. rewrite H14 in I10.
    assert (I11 : x <> x0). lra.
    apply H12 in I11 as I13. apply H11 in I11 as I12.
    rewrite I12; rewrite I13.
    assert (I14 : ξ ∈ Neighbor0 x0 δ').
    { apply AxiomII.
      split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    apply H15 in I14 as I15.
    destruct I15 as [I15 I16].
    apply derEqual in I15; apply derEqual in I16.
    rewrite <- I15; rewrite <- I16.
    assert (I17 : (0 - f1[x]) / (0 - g1[x]) = f1[x]/g1[x]).
    { field. apply H19. apply AxiomII. split.
      - apply Abs_not_eq_0; lra.
      - apply Abs_R. lra. }
    rewrite I17 in I10.
    symmetry. assumption. }
  assert (H22 : Function {` λ x y, y = f [x] / g [x] `}).
  { intros x1 y1 z1 I1 I2. applyAxiomII' I1.
    applyAxiomII' I2. rewrite I2.
    assumption. }
  split; auto. unfold limit in H4.
  destruct H4 as [H4 [δ1' [H23 [H24 H25]]]].
  exists δ1'. split; try lra. split.
  - intros x1 I1. apply AxiomII. exists (f[x1]/g[x1]).
    apply AxiomII'. reflexivity.
  - intros ε I1. apply H25 in I1 as I2.
    destruct I2 as [δ [[I2 I3] I4]].
    generalize (Lemma1 δ' δ H2 I2).
    intros [δ1 [I5 [I6 I7]]].
    exists δ1. split; try lra. intros x I8.
    apply Lemma2 in I8 as I9.
    destruct I9 as [I9 I10].
    assert (I11 : {` λ x1 y,
      y = f[x1] / g[x1] `} [x] = f[x]/g[x]).
    { apply f_x; auto. apply AxiomII'.
      reflexivity. }
    rewrite I11.
    assert (I12 : ∀ x, {` λ x0 y,
      y = f '[x0] / g '[x0] `} [x]
      = f '[x] / g '[x]).
    { intro x1. apply f_x; auto. apply AxiomII'.
      reflexivity. }
    apply Rdichotomy in I9 as [I9 | I9].
    + assert (J1 : x0 - δ' < x < x0). lra.
      apply H21 in J1 as J2.
      destruct J2 as [ξ [J2 J3]].
      rewrite J3. assert (J4 : 0 < Abs[ξ - x0] < δ).
      { split.
        - apply Abs_not_eq_0; lra.
        - apply Abs_R. lra. }
      apply I4 in J4. rewrite I12 in J4.
      assumption.
    + assert (J1 : x0 < x < x0 + δ'). lra.
      apply H20 in J1 as J2.
      destruct J2 as [ξ [J2 J3]].
      rewrite J3. assert (J4 : 0 < Abs[ξ - x0] < δ).
      { split.
        - apply Abs_not_eq_0; lra.
        - apply Abs_R. lra. }
      apply I4 in J4. rewrite I12 in J4.
      assumption.
Qed.

Lemma Lemma6_1 : ∀ (f g: Fun) (x0 A : R) (n : nat),
  (∀ k, (k < n)%nat -> limit (dN f k) x0 0
  /\ limit (dN g k) x0 0) ->
  (∀ k, (0 < k <= n)%nat ->
    (∃ δ', δ' > 0 /\ Neighbor0 x0 δ' ⊂ dom[dN f k] /\
    Neighbor0 x0 δ' ⊂ dom[dN g k] /\
    (∀ x, x ∈ Neighbor0 x0 δ' -> (dN g k)[x] <> 0))) ->
  limit {` λ x y, y = (dN f n)[x] / (dN g n)[x] `} x0 A ->
  limit {` λ x y, y = f[x]/g[x] `} x0 A.
Proof.
  intros f g x0 A n. induction n as [|n IHn].
  - intros H0 H1 H2. simpl in H2. assumption.
  - intros H0 H1 H2. assert (H3 : limit {` λ x y,
      y = (dN f n)[x] / (dN g n)[x] `} x0 A).
    { apply Theorem6_7; try apply H0;
      try apply Nat.lt_succ_diag_r.
      - assert (J1 : (0 < S n <= S n)%nat).
        { split; [apply gt_Sn_O | apply le_n]. }
        apply H1 in J1 as J2.
        destruct J2 as [δ' [J2 [J3 [J4 J5]]]].
        exists δ'. split; auto.
        intros x J6. apply J3 in J6 as J7.
        apply J4 in J6 as J8.
        apply J5 in J6 as J9. rewrite Lemma5_8 in J9.
        applyAxiomII J8. destruct J8 as [y2 J8].
        applyAxiomII J7. destruct J7 as [y1 J7].
        applyAxiomII' J8; applyAxiomII' J7.
        repeat split; [exists y1 | exists y2 | auto]; auto.
      - assert (I1 : {` λ x y, y = 
        (dN f (S n)) [x] / (dN g (S n)) [x] `} =
        {` λ x y, y = dN f n '[ x] / dN g n '[ x] `}).
        { apply AxiomI. intros [x y]; split; intro J1;
          applyAxiomII' J1; apply AxiomII'.
          - rewrite <- Lemma5_8. rewrite <- Lemma5_8.
            assumption.
          - rewrite Lemma5_8. rewrite Lemma5_8.
            assumption. }
        rewrite I1 in H2. assumption. }
    apply IHn; auto. intros k [H4 H5].
    assert (H6 : (0 < k <= S n)%nat).
    { split; auto. }
    apply H1 in H6 as [δ' [H7 [H8 [H9 H10]]]].
    exists δ'. repeat split; auto.
Qed.


End A6_2.

Export A6_2.