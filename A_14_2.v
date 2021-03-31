Require Export A_14_1.

Module A14_2.

(* 定义：函数f在x0处的泰勒公式余项 *)
Definition TaylorRn f n x x0 :=
  f[x] - (Σ {` λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k `} n).

Theorem Theorem14_11 : ∀ f r x x0,
  0 < r -> -r < x-x0 < r
  -> limit_seq {` λ n s, s = TaylorRn f n x x0 `} 0
  -> limit_seq {` λ n s, s = Σ {` λ k v, v = (dN f k)[x0] /
      (INR (k!)) * (x - x0)^^k `} n `} f[x].
Proof.
  intros f r x x0 H0 H1 H2.
  split; try apply FunIsSeq.
  intros ε H3. apply H2 in H3 as H4.
  destruct H4 as [N H4].
  exists N. intros n H5. apply H4 in H5.
  rewrite FunValueR in H5.
  rewrite FunValueR. unfold TaylorRn in H5.
  rewrite Rminus_0_r in H5.
  rewrite Abs_eq_neg. rewrite Ropp_minus_distr.
  assumption.
Qed.

End A14_2.

Export A14_2.