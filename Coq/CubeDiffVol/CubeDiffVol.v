Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import Psatz.

Definition cube_vol : R -> R := fun h' => Rpower h' 3.

Theorem Rpower_recip_inv : forall (x k : R), 0 < x -> k <> 0 -> Rpower (Rpower x k) (1/k) = x.
Proof.
  intros x k Hx Hk.
  rewrite Rpower_mult.
  rewrite <- Rpower_1.
  - f_equal.
    field_simplify_eq.
    + reflexivity.
    + apply Hk.
  - apply Hx.
Qed.

Theorem Rmult_inv : forall (num denom : R), denom <> 0 -> num / denom = num * (/ denom).
Proof.
  intros.
  lra.
Qed.

Theorem Rpower_Ropp_corollary : forall x y:R, 0 < x -> Rpower (/ x) y = Rpower x (-y).
Proof.
  intros.
  rewrite <- (Rpower_1 x) at 1 by lra.
  rewrite <- (Rpower_Ropp x).
  rewrite (Rpower_mult x (- (1)) y).
  f_equal.
  field_simplify_eq.
  reflexivity.
Qed.

Theorem Rpower_Ropp_corollary_2 : forall x y:R, 0 < x -> Rpower (/ x) y = /Rpower x y.
Proof.
  intros.
  rewrite Rpower_Ropp_corollary by lra.
  rewrite Rpower_Ropp.
  reflexivity.
Qed.

Lemma Rpower_2_3 : Rpower 2 3 = 8.
Proof.
  assert (8 = 2^3) by lra.
  rewrite H. clear H.
  assert (0 < 2) by lra.
  (* Use the `Rpower_pow` theorem for natural numbers *)
  rewrite <- (Rpower_pow 3 2 H).
  (* INR 3 converts the natural number 3 to the real number 3 *)
  simpl.
  f_equal.
  field_simplify.
  reflexivity.
Qed.

Lemma Rpower_3_3 : Rpower 3 3 = 27.
Proof.
  assert (27 = 3^3) by lra.
  rewrite H. clear H.
  assert (0 < 3) by lra.
  (* Use the `Rpower_pow` theorem for natural numbers *)
  rewrite <- (Rpower_pow 3 3 H).
  (* INR 3 converts the natural number 3 to the real number 3 *)
  simpl.
  f_equal.
  field_simplify.
  reflexivity.
Qed.

Theorem cube_diff_vol : forall h, 0 < h -> cube_vol h - cube_vol (h*(2/3)) = cube_vol (h * (Rpower 19 (/3))/3).
Proof.
  intros.
  (*
    cube_vol h - cube_vol (h*2/3) = cube_vol (h * 19^(1/3)/3)
  *)

  unfold cube_vol at 1 2.
  (*
    h^3 - (h*2/3)^3 = cube_vol (h * 19^(1/3)/3)
  *)

  assert (0 < 2/3) by lra.
  rewrite <- (Rpower_mult_distr h (2 / 3) 3 H H0). clear H0.
  rewrite <- (Rmult_1_r (Rpower h 3)) at 1.
  rewrite <- Rmult_minus_distr_l.
  (*
    h^3 * (1 - (2/3)^3) = cube_vol (h * 19^(1/3)/3)
  *)

  assert (1 - Rpower (2 / 3) 3 = 19/(Rpower 3 3)) by (
    rewrite (Rmult_inv 2 3) by lra;
    assert (0 < 2) by lra;
    assert (0 < /3) by lra;
    rewrite <- (Rpower_mult_distr 2 (/3) 3 H0 H1); clear H0 H1;
    rewrite (Rpower_Ropp_corollary_2 3 3) by lra;
    assert (Rpower 3 3 <> 0) by (rewrite Rpower_3_3; lra);
    rewrite <- (Rinv_r (Rpower 3 3) H0);
    rewrite <- (Rmult_minus_distr_r (/ Rpower 3 3) (Rpower 3 3) (Rpower 2 3));
    rewrite Rmult_inv by lra;
    f_equal;
    rewrite Rpower_2_3;
    rewrite Rpower_3_3;
    lra
  ).
  rewrite H0. clear H0.
  (*
    h^3 * 19/3^3 = cube_vol (h * 19^(1/3)/3)
  *)

  assert (0 < 19) by lra.
  assert (/3 <> 0) by lra.
  rewrite <- (Rpower_recip_inv 19 (/3) H0 H1) at 1. clear H0 H1.
  replace (1 / / 3) with 3 by lra.
  (*
    h^3 * 19^(1/3)^3/3^3 = cube_vol (h * 19^(1/3)/3)
  *)

  assert (Rpower 3 3 <> 0) by (rewrite Rpower_3_3; lra).
  rewrite (Rmult_inv (Rpower (Rpower 19 (/ 3)) 3) (Rpower 3 3) H0). clear H0.
  rewrite <- Rpower_Ropp_corollary_2 by lra.
  assert (0 < Rpower 19 (/ 3)) by (unfold Rpower; apply exp_pos).
  assert (0 < /3) by lra.
  rewrite (Rpower_mult_distr ((Rpower 19 (/ 3))) (/ 3) 3 H0 H1). clear H1.
  (*
    h^3 * (19^(1/3)*(1/3))^3 = cube_vol (h * 19^(1/3)/3)
  *)

  assert (0 < Rpower 19 (/ 3) * / 3) by lra. clear H0.
  rewrite (Rpower_mult_distr h (Rpower 19 (/ 3) * / 3) 3 H H1). clear H H1.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_inv by lra.
  (*
    (h*19^(1/3)/3)^3 = cube_vol (h * 19^(1/3)/3)
  *)

  fold (cube_vol (h * Rpower 19 (/ 3) / 3)).
  (*
    cube_vol (h*19^(1/3)/3) = cube_vol (h * 19^(1/3)/3)
  *)

  reflexivity.
Qed.
