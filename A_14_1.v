Require Export A_13_2.

Module A14_1.

(* 幂级数 *)

(* 定义：数列u对应的幂函数列 *)
Definition PowSeq u :=
  {` λ n f, f = {` λ x y, y = u[n] * x^^n `} `}.

Lemma Lemma14_1_1 : ∀ u x, VFunSeq (PowSeq u) x
  = {` λ n s, s = u[n] * x^^n `}.
Proof.
  intros u x. apply AxiomI.
  intros [n s]. unfold PowSeq.
  split; intros H0;
  applyAxiomII' H0; apply AxiomII'.
  - rewrite FunValueFun in H0.
    rewrite FunValueR in H0.
    assumption.
  - rewrite FunValueFun.
    rewrite FunValueR.
    assumption.
Qed.

Lemma Lemma14_1_2 : ∀ u n x, (PowSeq u)[`n`][x] = u[n] * x^^n.
Proof.
  intros u n x. unfold PowSeq. rewrite FunValueFun.
  rewrite FunValueR. reflexivity.
Qed.

Lemma Lemma14_1_3 : ∀ u n x, (VFunSeq (PowSeq u) x)[n] = u[n] * x^^n.
Proof.
  intros u n x. rewrite Lemma14_1_1.
  repeat rewrite FunValueR. reflexivity.
Qed.

Lemma Lemma14_1_4 : ∀ f x,
  VFunSeq (PowSeq {` λ n s, s = f n `}) x =
  {` λ n s, s = (f n) * x^^n `}.
Proof.
  intros f x. rewrite Lemma14_1_1.
  apply AxiomI.
  intros [n s]. unfold PowSeq.
  split; intros H0;
  applyAxiomII' H0; apply AxiomII'.
  - rewrite FunValueR in H0. assumption.
  - rewrite FunValueR. assumption.
Qed.

(* 定义：幂级数在x处收敛于a *)
Definition PowSerConXA u x a :=
  limit_seq (Series (VFunSeq (PowSeq u) x)) a.
(* 定义：幂级数在x处收敛 *)
Definition PowSerConX u x := ConSer (VFunSeq (PowSeq u) x).
(* 定义：幂级数在x处绝对收敛 *)
Definition AbsoPowSerConX u x := AbsoluteCon (VFunSeq (PowSeq u) x).
(* 定义：幂级数在x处发散 *)
Definition PowSerDivX u x := DivSer (VFunSeq (PowSeq u) x).

(* 定理14.1：阿贝尔定理 *)
Theorem Theorem14_1_1 : ∀ u x0 x, PowSerConX u x0
  -> Abs[x] < Abs[x0] -> AbsoPowSerConX u x.
Proof.
  intros u x0 x H0 H1.
  unfold PowSerConX in H0.
  rewrite Lemma14_1_1 in H0.
  assert (H2 : IsSeq {`λ n s, s = u[n] * x0^^n `}).
  { apply FunIsSeq. }
  apply Theorem12_1' in H0 as H3; auto.
  assert (H4 : ∃ M, ∀ n,  Abs[u[n] * x0^^n] < M).
  { assert (I1 : Convergence {`λ n s, s = u[n] * x0^^n `}).
    { exists 0. assumption. }
    apply Theorem2_3' in I1 as [M I1].
    exists (M + 1). intros n.
    generalize (I1 n). rewrite FunValueR. lra. }
  destruct H4 as [M H4].
  unfold AbsoPowSerConX. rewrite Lemma14_1_1.
  unfold AbsoluteCon.
  assert (H5 : {` λ n v, v = Abs[{` λ n0 s,
    s = u[n0] * x ^^ n0 `}[n]] `} =
    {` λ n v, v = Abs[u[n] * x^^n] `}).
  { apply AxiomI; intros [n s];
    split; intro I1;
    applyAxiomII' I1; apply AxiomII'.
    - rewrite FunValueR in I1. assumption.
    - rewrite FunValueR. assumption. }
  rewrite H5. clear H5.
  generalize (Abs_Rge0 x); intros H5.
  assert (H8 : 0 < Abs[x0]). lra.
  assert (H6 : x0 <> 0).
  { apply Abs_not_eq_0. assumption. }
  assert (H7 : -1 < Abs[x/x0] < 1).
  { split.
    - generalize (Abs_Rge0 (x/x0)). lra.
    - rewrite Abs_div; auto.
      apply Rmult_lt_reg_r with (r := Abs[x0]); auto.
      assert (I1 : Abs[x] / Abs[x0] * Abs[x0] = Abs[x]).
      { field. lra. }
      rewrite I1. lra. }
  assert (H9 : ∀ n, Abs[u[n] * x^^n] <= M * Abs[x/x0]^^n).
  { intros n. assert (I1 : u[n] * x^^n
      = u[n] * x0^^n * ((x^^n)/(x0^^n))).
    { field. apply Lemma6_3_5. assumption. }
    rewrite I1. clear I1. rewrite Abs_mult.
    assert (I1 : Abs[x^^n / x0^^n] = Abs[x/x0]^^n).
    { induction n as [|n IHn].
      - simpl. rewrite Abs_gt; lra.
      - simpl. rewrite <- IHn.
        rewrite <- Abs_mult.
        assert (J1 : x * x ^^ n / (x0 * x0 ^^ n)
          = x / x0 * (x ^^ n / x0 ^^ n)).
        { field. split; [apply Lemma6_3_5 | assumption];
          assumption. }
        rewrite J1. reflexivity. }
    rewrite I1.
    apply Rmult_le_compat_r.
    - apply Lemma12_2_3. apply Rge_le.
      apply Abs_Rge0.
    - left. apply H4. }
  apply Theorem12_6' with (v := {` λ n s,
    s = M * Abs [x / x0] ^^ n `}).
  - intros n. rewrite FunValueR.
    apply Rge_le. apply Abs_Rge0.
  - intros n. rewrite FunValueR.
    generalize (Abs_Rge0 (u[n] * x^^n)).
    generalize (H9 n). lra.
  - intros n. repeat rewrite FunValueR.
    apply H9.
  - exists ((M / (1 - Abs [x / x0]))).
    apply SeriesProportionalSequence.
    assumption.
Qed.

Theorem Theorem14_1_2 : ∀ u x0 x, PowSerDivX u x0
  -> Abs[x0] < Abs[x] -> PowSerDivX u x.
Proof.
  intros u x0 x H0 H1 H2.
  generalize (Theorem14_1_1 u x x0 H2 H1).
  intros H3. apply Theorem12_12 in H3.
  apply H0. assumption.
Qed.

(* 收敛半径 *)

(* 定义：r是幂级数u的收敛半径 *)
Definition ConRadius u r := 0 <= r /\
  (∀ x, Abs[x] < r -> AbsoPowSerConX u x) /\
  (∀ x, r < Abs[x] -> PowSerDivX u x).
(* 定义：幂级数u的收敛半径是无穷大 *)
Definition ConRadiusInf u := ∀ x, AbsoPowSerConX u x.

(* 定理：任何幂级数均存在收敛半径 *)
Theorem ExistRadius : ∀ u, ConRadiusInf u \/ (∃ r, ConRadius u r).
Proof.
  intros u. destruct classic with (P :=
    ConRadiusInf u) as [H0 | H0]; [left | right]; auto.
  apply not_all_ex_not in H0 as [r0 H0].
  assert (H1 : NotEmpty \{ λ a, 0 <= a /\ PowSerDivX u a \}).
  { apply NNPP. intros I1.
    assert (I2 : ∀ x, ~ (x ∈ \{ λ a, 0 <= a /\ PowSerDivX u a \})).
    { apply not_ex_all_not. apply I1. }
    assert (I3 : ∀ x, 0 <= x -> PowSerConX u x).
    { intros x J3. generalize (I2 x); intros J1.
      apply NNPP. intros J2. apply J1.
      apply AxiomII. split; auto. }
    apply H0. assert (I4 : 0 <= Abs[r0] + 1).
    { generalize (Abs_Rge0 r0). lra. }
    apply Theorem14_1_1 with (x0 := Abs[r0] + 1); auto.
    apply Rle_ge in I4.
    rewrite (Abs_ge (Abs[r0] + 1)); auto.
    lra. }
  apply Sup_inf_principle in H1 as H2.
  destruct H2 as [H2 H3]. clear H2.
  assert (H2 : ∃ L, Lower \{ λ a, 0 <= a /\ PowSerDivX u a \} L).
  { exists 0. unfold Lower. intros x I1.
    applyAxiomII I1. lra. }
  apply H3 in H2 as [r H2]. clear H3.
  exists r. assert (H3 : 0 <= r).
  { apply NNPP. intros I1. apply Rnot_le_lt in I1.
    destruct H2 as [I2 I3].
    assert (I4 : r/2 > r). lra.
    apply I3 in I4 as [a [I4 I5]].
    applyAxiomII I4. lra. }
  destruct H2 as [H2 H4].
  repeat split; auto; intros x I1.
  - unfold Lower in H2.
    generalize (Abs_Rge0 x); intros I2.
    assert (I3 : (Abs[x] + r)/2 >= 0). lra.
    assert (I4 : PowSerConX u ((Abs[x] + r)/2)).
    { apply NNPP. intros I4.
      assert (J1 : (Abs[x] + r)/2 >= r).
      { apply H2. apply AxiomII.
        split; [lra | auto]. }
      lra. }
    apply Theorem14_1_1 with (x0 := (Abs[x] + r)/2); auto.
    rewrite (Abs_ge ((Abs[x] + r)/2)); auto.
    lra.
  - assert (I2 : (r + Abs[x])/2 > r). lra.
    apply H4 in I2 as I3.
    destruct I3 as [x0 [I3 I4]].
    applyAxiomII I3. destruct I3 as [I3 I5].
    assert (I6 : Abs[x0] < Abs[x]).
    { apply Abs_R. split; lra. }
    eapply Theorem14_1_2; eauto.
Qed.

Lemma Lemma14_1_5 : ∀ a, 0 <= Abs[a].
Proof.
  intros a. generalize (Abs_Rge0 a). lra.
Qed.

Lemma Lemma14_1_6 : ∀ a n, Abs[a^^n] = Abs[a]^^n.
Proof.
  intros a n. induction n as [|n IHn].
  - simpl. rewrite Abs_ge; lra.
  - simpl. rewrite Abs_mult.
    rewrite IHn. reflexivity.
Qed.

Lemma Lemma14_1_7 : ∀ a, 0 <= a -> Abs[a] = a.
Proof.
  intros a H0. apply Abs_ge. lra.
Qed.

Lemma Lemma14_1_8 : ∀ a b n, 0 <= a -> 0 <= b
  -> (0 < n)%nat -> a^^n = b^^n -> a = b.
Proof.
  intros a b n H0 H1 H2 H3.
  apply NNPP. intros H4.
  apply Rdichotomy in H4.
  destruct H4 as [H4 | H4];
  apply Lemma12_2_4 with (n := n) in H4; auto;
  lra.
Qed.

Lemma Lemma14_1_9 : ∀ r n, (0 < n)%nat -> 0 <= r
  -> (n √ r)^^n = r.
Proof.
  intros r n H0 H1.
  apply Lemma12_2_2; auto.
Qed.

Lemma Lemma14_1_10 : ∀ a b n, (a*b)^^n = a^^n * b^^n.
Proof.
  intros a b n.
  induction n as [|n IHn].
  - simpl. field.
  - simpl. rewrite IHn. field.
Qed.

Lemma Lemma14_1_11 : ∀ a b n, 0 <= a -> 0 <= b
  -> (0 < n)%nat -> n √ (a * b) = (n √ a) * (n √ b).
Proof.
  intros a b n H0 H1 H2.
  apply Lemma14_1_8 with (n := n); auto.
  - apply Lemma12_2_2; auto.
    apply Rmult_le_pos; auto.
  - apply Rmult_le_pos; apply Lemma12_2_2; auto.
  - assert (0 <= a * b).
    { apply Rmult_le_pos; auto. }
    rewrite Lemma14_1_9; auto.
    rewrite Lemma14_1_10.
    repeat rewrite Lemma14_1_9; auto.
Qed.

Lemma Lemma14_1_12 : ∀ a n, 0 <= a
  -> (0 < n)%nat -> n √ (a^^n) = a.
Proof.
  intros a n H0 H1.
  apply Lemma12_2_6; auto.
Qed.

Theorem Lemma14_2 : ∀ u ρ x,
  limit_seq {` λ n s, s = n √ (Abs[u[n]]) `} ρ
  -> limit_seq {` λ n v, v = n √ {` λ n0 v0,
        v0 = Abs [(VFunSeq (PowSeq u) x) [n0]] `} [n] `}
     (ρ * Abs [x]).
Proof.
  intros u ρ x H0.
  assert (H1 : {` λ n v, v = n √ {` λ n0 v0,
    v0 = Abs [(VFunSeq (PowSeq u) x) [n0]] `} [n] `}
    = {` λ n v, v = n √ (Abs[u[n]] * (Abs[x])^^n) `}).
  { apply Lemma12_3_2. intros n.
    rewrite FunValueR. rewrite Lemma14_1_3.
    rewrite Abs_mult. rewrite Lemma14_1_6.
    reflexivity. }
  rewrite H1. clear H1.
  split; try apply FunIsSeq.
  intros ε H1. destruct classic with (P := x = 0) as [H2 | H2].
  - exists O. intros n I1.
    assert (I2 : Abs[x] = 0).
    { rewrite Abs_ge; lra. }
    rewrite I2 in *. rewrite FunValueR.
    rewrite Lemma6_3_4; auto.
    repeat rewrite Rmult_0_r.
    pattern 0 at 1. rewrite <- (Lemma6_3_4 n); auto.
    rewrite Lemma14_1_12; [apply Abs_R; lra | lra | auto].
  - apply Abs_not_eq_0 in H2 as I1.
    assert (I2 : ε/Abs[x] > 0).
    { apply Rdiv_lt_0_compat; auto. }
    apply H0 in I2 as I3.
    destruct I3 as [N I3].
    exists N. intros n I4.
    rewrite FunValueR. apply I3 in I4 as I5.
    rewrite FunValueR in I5.
    apply Nat.lt_lt_0 in I4 as I6.
    assert (I7 : n √ (Abs [u [n]] * Abs [x] ^^ n)
      = n √ (Abs [u [n]]) * Abs [x]).
    { generalize (Lemma14_1_5 (u[n])); intros J1.
      assert (J2 : 0 <= Abs[x]^^n).
      { apply Lemma12_2_3. left; assumption. }
      rewrite Lemma14_1_11; auto.
      rewrite Lemma14_1_12; auto.
      left; auto. }
    rewrite I7. clear I7.
    assert (I7 : n √ Abs [u [n]] * Abs [x] - ρ * Abs [x]
      = (n √ Abs [u [n]] - ρ) * Abs [x]).
    field. rewrite I7. clear I7.
    rewrite Abs_mult.
    rewrite (Abs_gt Abs[x]); auto.
    assert (I7 : 0 < /Abs[x]).
    { apply Rinv_0_lt_compat. assumption. }
    apply Rmult_lt_reg_r with (r := /Abs[x]); auto.
    rewrite Rinv_r_simpl_l; lra.
Qed.

Theorem Theorem14_2_1 : ∀ u ρ,
  limit_seq {` λ n s, s = n √ (Abs[u[n]]) `} ρ
  -> 0 < ρ -> ConRadius u (1/ρ).
Proof.
  intros u ρ H0 H1. unfold ConRadius.
  assert (H2 : 0 < 1/ρ).
  { unfold Rdiv. rewrite Rmult_1_l.
    apply Rinv_0_lt_compat.
    assumption. }
  assert (H3 : ∀x : R,Abs [x] < 1 / ρ -> AbsoPowSerConX u x).
  { intros x I1. apply Theorem12_8_3 with (q := ρ*Abs[x]).
    - apply FunIsSeq.
    - intros n. rewrite FunValueR.
      apply Lemma14_1_5.
    - unfold Rdiv in H2. rewrite Rmult_1_l in H2.
      apply Rmult_lt_reg_r with (r := /ρ); auto.
      assert (I2 : ρ * Abs [x] * / ρ = Abs[x]).
      { field. lra. }
      rewrite I2. apply I1.
    - apply Lemma14_2. assumption. }
  split; [lra | split]; auto.
  assert (H4 : ∀ x, 1 / ρ < Abs [x] -> ~ AbsoPowSerConX u x).
  { intros x I1. apply Theorem12_8_4 with (q := ρ*Abs[x]).
    - apply FunIsSeq.
    - intros n. rewrite FunValueR.
      apply Lemma14_1_5.
    - apply Rmult_lt_compat_l with (r := ρ) in I1 as I2; auto.
      assert (J1 : ρ * (1 / ρ) = 1).
      { field. lra. }
      rewrite <- J1. assumption.
    - apply Lemma14_2. assumption. }
  generalize (ExistRadius u). intros H5.
  assert (H6 : ∃ r, ConRadius u r).
  { destruct H5 as [I1 | I1]; auto.
    exfalso. apply (H4 (1/ρ + 1)); try apply I1.
    rewrite Abs_gt; lra. }
  clear H5. destruct H6 as [r [H6 [H7 H8]]].
  assert (H9 : r = 1 / ρ).
  { apply NNPP. intros I1.
    apply Rdichotomy in I1.
    destruct I1 as [I1 | I1].
    - assert (J1 : Abs[(r + 1/ρ)/2] < 1/ρ).
      { rewrite Abs_ge; lra. }
      apply H3 in J1 as J2.
      apply (H8 ((r + 1/ρ)/2)).
      + rewrite Abs_ge; lra.
      + apply Theorem12_12. assumption.
    - apply (H4 ((r + 1/ρ)/2)).
      + rewrite Abs_ge; lra.
      + apply H7. rewrite Abs_ge; lra. }
  rewrite <- H9. assumption.
Qed.

Theorem Theorem14_2_2 : ∀ u,
  limit_seq {` λ n s, s = n √ (Abs[u[n]]) `} 0
  -> ConRadiusInf u.
Proof.
  intros u H0 x.
  apply Theorem12_8_3 with (q := 0*Abs[x]).
  - apply FunIsSeq.
  - intros n. rewrite FunValueR.
    apply Lemma14_1_5.
  - rewrite Rmult_0_l. lra.
  - apply Lemma14_2. assumption.
Qed.

Theorem Theorem14_2_3 : ∀ u,
  PosInfSeq {` λ n s, s = n √ (Abs[u[n]]) `}
  -> ConRadius u 0.
Proof.
  intros u H0.
  assert (H1 : ∀ x, 0 < Abs [x] -> ~ AbsoPowSerConX u x).
  { intros x I1. apply Theorem12_8_5.
    - apply FunIsSeq.
    - intros n. rewrite FunValueR.
      apply Lemma14_1_5.
    - assert (I2 : {` λ n v, v = n √ {` λ n0 v0,
        v0 = Abs [(VFunSeq (PowSeq u) x) [n0]] `} [n] `}
        = {` λ n v, v = n √ (Abs[u[n]] * (Abs[x])^^n) `}).
      { apply Lemma12_3_2. intros n.
        rewrite FunValueR. rewrite Lemma14_1_3.
        rewrite Abs_mult. rewrite Lemma14_1_6.
        reflexivity. }
      rewrite I2. clear I2.
      split; try apply FunIsSeq.
      intros M H1. apply Abs_not_eq_0 in I1 as I2.
      assert (I3 : M/Abs[x] > 0).
      { apply Rdiv_lt_0_compat; auto. }
      apply H0 in I3 as I4.
      destruct I4 as [N I4].
      exists N. intros n I5.
      rewrite FunValueR. apply I4 in I5 as I6.
      rewrite FunValueR in I6.
      apply Nat.lt_lt_0 in I5 as I7.
      assert (I8 : n √ (Abs [u [n]] * Abs [x] ^^ n)
        = n √ (Abs [u [n]]) * Abs [x]).
      { generalize (Lemma14_1_5 (u[n])); intros J1.
        assert (J2 : 0 <= Abs[x]^^n).
        { apply Lemma12_2_3. left; assumption. }
        rewrite Lemma14_1_11; auto.
        rewrite Lemma14_1_12; auto.
        left; auto. }
      rewrite I8. clear I8.
      assert (I8 : 0 < /Abs[x]).
      { apply Rinv_0_lt_compat. assumption. }
      apply Rmult_lt_reg_r with (r := /Abs[x]); auto.
      rewrite Rinv_r_simpl_l; lra. }
  generalize (ExistRadius u). intros H5.
  assert (H6 : ∃ r, ConRadius u r).
  { destruct H5 as [I1 | I1]; auto.
    exfalso. apply (H1 1); try apply I1.
    rewrite Abs_gt; lra. }
  clear H5. destruct H6 as [r [H6 [H7 H8]]].
  assert (H9 : r = 0).
  { apply NNPP. intros I1.
    apply Rdichotomy in I1.
    destruct I1 as [I1 | I1].
    - lra.
    - apply (H1 (r/2)).
      + rewrite Abs_ge; lra.
      + apply H7. rewrite Abs_ge; lra. }
  rewrite <- H9. repeat split; assumption.
Qed.

Theorem Theorem14_4_1 : ∀ u r a b, ConRadius u r
  -> a < b -> (\[a, b\]) ⊂ \(-r, r\)
  -> FunSerUniCon (PowSeq u) (\[a, b\]).
Proof.
  intros u r a b H0 H7 H1.
  assert (H2 : ∃ x0, (x0 = Abs[a] \/ x0 = Abs[b])
    /\ Abs[a] <= x0 /\ Abs[b] <= x0).
  { destruct (Rlt_or_le Abs[a] Abs[b]) as [I1 | I1].
    - exists Abs[b]. lra.
    - exists Abs[a]. lra. }
  destruct H2 as [x0 [H2 [H3 H4]]].
  assert (H5 : ∀ x, x ∈ (\[a, b\]) -> Abs[x] <= x0).
  { intros x I1. applyAxiomII I1.
    apply Abs_le_R in H3.
    apply Abs_le_R in H4.
    apply Abs_le_R. lra. }
  assert (H6 : x0 < r).
  { assert (I1 : Abs[a] < r).
    { apply Abs_R.
      assert (J1 : a ∈ \(-r, r\)).
      { apply H1. apply AxiomII. lra. }
      applyAxiomII J1. lra. }
    assert (I2 : Abs[b] < r).
    { apply Abs_R.
      assert (J1 : b ∈ \(-r, r\)).
      { apply H1. apply AxiomII. lra. }
      applyAxiomII J1. lra. }
    lra. }
  assert (H8 : 0 <= x0).
  { generalize (Abs_Rge0 a). lra. }
  assert (H9 : AbsoPowSerConX u x0).
  { assert (I1 : Abs[x0] < Abs[(x0 + r)/2]).
    { apply Rle_ge in H8.
      repeat rewrite Abs_ge; lra. }
    assert (I2 : Abs [(x0 + r)/2] < r).
    { rewrite Abs_ge; lra. }
    apply H0 in I2. apply Theorem12_12 in I2.
    eapply Theorem14_1_1; eauto. }
  unfold AbsoPowSerConX in H9.
  rewrite Lemma14_1_1 in H9.
  unfold AbsoluteCon in H9.
  apply Theorem13_5 with (M := {` λ n v, v =
    Abs[{` λ n0 s, s = u[n0] * x0^^n0 `} [n]] `}); auto.
  - apply FunIsFunSeq. intros n.
    apply IsFun.
  - intros n x I1.
    unfold PowSeq. rewrite FunValueFun.
    apply AxiomII. exists (u[n] * x^^n).
    apply AxiomII'. reflexivity.
  - intros n. rewrite FunValueR.
    apply Rge_le. apply Abs_Rge0.
  - intros x n I1. rewrite Lemma14_1_2.
    repeat rewrite FunValueR.
    apply H5 in I1.
    repeat rewrite Abs_mult.
    generalize (Lemma14_1_5 u[n]). intros I2.
    apply Rmult_le_compat_l; auto.
    repeat rewrite Lemma14_1_6.
    apply Lemma12_2_7; try apply Lemma14_1_5.
    rewrite (Abs_ge x0); lra.
Qed.

Theorem Theorem14_4_2 : ∀ u a b, ConRadiusInf u
  -> a < b -> FunSerUniCon (PowSeq u) (\[a, b\]).
Proof.
  intros u a b H0 H7.
  assert (H2 : ∃ x0, (x0 = Abs[a] \/ x0 = Abs[b])
    /\ Abs[a] <= x0 /\ Abs[b] <= x0).
  { destruct (Rlt_or_le Abs[a] Abs[b]) as [I1 | I1].
    - exists Abs[b]. lra.
    - exists Abs[a]. lra. }
  destruct H2 as [x0 [H2 [H3 H4]]].
  assert (H5 : ∀ x, x ∈ (\[a, b\]) -> Abs[x] <= x0).
  { intros x I1. applyAxiomII I1.
    apply Abs_le_R in H3.
    apply Abs_le_R in H4.
    apply Abs_le_R. lra. }
  assert (H8 : 0 <= x0).
  { generalize (Abs_Rge0 a). lra. }
  generalize (H0 x0); intros H9.
  unfold AbsoPowSerConX in H9.
  rewrite Lemma14_1_1 in H9.
  unfold AbsoluteCon in H9.
  apply Theorem13_5 with (M := {` λ n v, v =
    Abs[{` λ n0 s, s = u[n0] * x0^^n0 `} [n]] `}); auto.
  - apply FunIsFunSeq. intros n.
    apply IsFun.
  - intros n x I1.
    unfold PowSeq. rewrite FunValueFun.
    apply AxiomII. exists (u[n] * x^^n).
    apply AxiomII'. reflexivity.
  - intros n. rewrite FunValueR.
    apply Rge_le. apply Abs_Rge0.
  - intros x n I1. rewrite Lemma14_1_2.
    repeat rewrite FunValueR.
    apply H5 in I1.
    repeat rewrite Abs_mult.
    generalize (Lemma14_1_5 u[n]). intros I2.
    apply Rmult_le_compat_l; auto.
    repeat rewrite Lemma14_1_6.
    apply Lemma12_2_7; try apply Lemma14_1_5.
    rewrite (Abs_ge x0); lra.
Qed.

(* 幂级数的和函数 *)
Definition sumPowSer u := {` λ x y, PowSerConXA u x y `}.

Lemma Lemma14_1_13 : ∀ u, Function (sumPowSer u).
Proof.
  intros u. intros x y z H0 H1.
  applyAxiomII' H0. applyAxiomII' H1.
  eapply Theorem2_2; eauto.
Qed.

Lemma Lemma14_6 : ∀ u D, FunSerUniCon (PowSeq u) D
  -> FunSerUniConF (PowSeq u) (sumPowSer u) D.
Proof.
  intros u D [S H0].
  assert (H1 : D ⊂ dom[sumPowSer u]).
  { intros x I1. apply AxiomII.
    exists S[x]. apply AxiomII'.
    split; [apply SeriesSeq | intros ε I2].
    apply H0 in I2 as I3.
    destruct I3 as [N I3]. exists N.
    intros n I4. generalize (I3 n x I4 I1).
    intros I5. rewrite SeriesValue.
    rewrite VFunSerNX in I5.
    assumption. }
  repeat split; auto; try apply H0; try apply Lemma14_1_13.
  assert (H2 : ∀ x, x ∈ D -> limit_seq
    (VFunSeq (FunSer (PowSeq u)) x) S[x]).
  { intros x I1. split; try apply VFunSeqIsSeq.
    intros ε I2. apply H0 in I2 as I3.
    destruct I3 as [N I3]. exists N.
    intros n I4. generalize (I3 n x I4 I1).
    intros I5. rewrite VFunSerXN.
    rewrite VFunSerNX in I5. assumption. }
  assert (H3 : ∀ x, x ∈ D -> limit_seq
    (VFunSeq (FunSer (PowSeq u)) x) (sumPowSer u)[x]).
  { intros x I1. split; try apply VFunSeqIsSeq.
    intros ε I2. apply H1 in I1 as I3.
    applyAxiomII I3. destruct I3 as [y I3].
    apply f_x in I3 as I6; try apply Lemma14_1_13.
    applyAxiomII' I3. apply I3 in I2 as I4.
    destruct I4 as [N I4]. exists N.
    intros n I5. rewrite I6.
    generalize (I4 n I5). intros I7.
    rewrite SeriesValue in I7.
    rewrite VFunSerXN. assumption. }
  intros ε H4. apply H0 in H4 as H5.
  destruct H5 as [N H5]. exists N.
  intros n x H6 H7. generalize (H5 n x H6 H7).
  intros H8. assert (H9 : S[x] = (sumPowSer u)[x]).
  { eapply Theorem2_2; eauto. }
  rewrite <- H9. assumption.
Qed.

Theorem Theorem14_6_1 : ∀ u r, ConRadius u r
  -> ContinuousOpen (sumPowSer u) (-r) r.
Proof.
  intros u r H0 x H1.
  assert (H2 : 0 < r).
  { destruct H0 as [I1 I2].
    destruct I1 as [I1 | I1]; lra. }
  assert (H3 : (x-r)/2 < (x+r)/2). lra.
  assert (H4 : (\[(x-r)/2, (x+r)/2\]) ⊂ \(-r, r\)).
  { intros a I1. applyAxiomII I1.
    apply AxiomII. lra. }
  generalize (Theorem14_4_1 u r ((x-r)/2) ((x+r)/2)
    H0 H3 H4). intros H5.
  apply Lemma14_6 in H5 as H6.
  assert (H7 : ∀ n, ContinuousClose
    (PowSeq u)[`n`] ((x-r)/2) ((x+r)/2)).
  { intros n.
    unfold PowSeq. rewrite FunValueFun.
    assert (I2 : {` λ x1 y, y = u [n] * x1 ^^ n `}
      = {` λ x1 y, y = u [n] * (x1 - 0) ^^ n `}).
    { apply Lemma12_3_2. intros x1.
      assert (I2 : x1 = x1 - 0). lra.
      rewrite <- I2. reflexivity. }
    rewrite I2.
    assert (I3 : ∀ x0, x0 ∈ dom[{` λ x1 y,
      y = u [n] * (x1 - 0) ^^ n `}]).
    { intros x0. apply AxiomII. exists (u [n] * (x0 - 0)^^n).
      apply AxiomII'. reflexivity. }
    split; [intros x0 I1 | split]; split;
      auto; rewrite FunValueR.
    - apply Lemma7'.
    - apply Theorem3_1. apply Lemma7'.
    - apply Theorem3_1. apply Lemma7'. }
  eapply Theorem13_12'; eauto; lra.
Qed.

Theorem Theorem14_6_2 : ∀ u, ConRadiusInf u
  -> ∀ x, Continuous (sumPowSer u) x.
Proof.
  intros u H0 x.
  assert (H3 : x-1 < x+1). lra.
  generalize (Theorem14_4_2 u (x-1) (x+1)
    H0 H3). intros H5.
  apply Lemma14_6 in H5 as H6.
  assert (H7 : ∀ n, ContinuousClose
    (PowSeq u)[`n`] (x-1) (x+1)).
  { intros n.
    unfold PowSeq. rewrite FunValueFun.
    assert (I2 : {` λ x1 y, y = u [n] * x1 ^^ n `}
      = {` λ x1 y, y = u [n] * (x1 - 0) ^^ n `}).
    { apply Lemma12_3_2. intros x1.
      assert (I2 : x1 = x1 - 0). lra.
      rewrite <- I2. reflexivity. }
    rewrite I2.
    assert (I3 : ∀ x0, x0 ∈ dom[{` λ x1 y,
      y = u [n] * (x1 - 0) ^^ n `}]).
    { intros x0. apply AxiomII. exists (u [n] * (x0 - 0)^^n).
      apply AxiomII'. reflexivity. }
    split; [intros x0 I1 | split]; split;
      auto; rewrite FunValueR.
    - apply Lemma7'.
    - apply Theorem3_1. apply Lemma7'.
    - apply Theorem3_1. apply Lemma7'. }
  eapply Theorem13_12'; eauto; lra.
Qed.

End A14_1.

Export A14_1.
