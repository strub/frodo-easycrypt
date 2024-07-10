require import AllCore IntDiv Real.
import RField.

op round (x: real): int = floor (x + inv 2%r).

op D: {int | 0 <= D <= 16} as D_bound.
op q = 2^D.
op B: {int | 0 <= B <= D} as B_bound.

(* 0 <= k < 2^B. *)
op ec k = k * q %/ 2^B. 

op dc c = round (ofint c * ofint (2^B) / ofint q) %% 2^B.

lemma foo (x: int) m n: 0 <= n => n <= m => x^m = x^n * x^(m-n).
proof.
    move => *.
    rewrite -(Ring.IntID.exprD_nneg x n (m-n) _ _) => //.
    rewrite subz_ge0 => //.
    have : m = n + (m - n). by ring.
    move => [#] <- //.
qed.

lemma ofint_hom (x y: int): ofint x * ofint y = ofint (x*y).
proof.
    rewrite /ofint !intmulr => />.
    smt().
qed.

lemma ofint_div (x: int): x <> 0 => ofint x / ofint x = 1%r.
proof.
   move => hx. apply unitrE.
   rewrite /ofint intmulr => />.
   smt().
qed.

lemma real_mul_div (x y: real): y <> 0%r => x * y / y = x.
proof.
move => h.
rewrite (eqr_div (x*y) y x 1%r) => />.
qed.

lemma pow2_gt0: forall x, 0 <= x => 0 < 2^x.
proof.
    elim /intind.
    + by rewrite Ring.IntID.expr0.
    + move => i hi0 hi1. rewrite Ring.IntID.exprSr => //. smt().
qed.

lemma real_neq_ltz x y: x <> y => x%r <> y%r.
proof.
    by smt().
qed.

lemma floor_add_lt1 x y: 0%r <= y < 1%r => floor (x%r + y) = x.
proof.
    move => h.
    rewrite floorP.
    smt().
qed.

(* I want to be able to ooperate on proof term just like the other data types *)
lemma decode_correctness k: 0 <= k < (2^B) => dc (ec k) = k.
proof.
    move => [#] hk1 hk2.
    rewrite /dc /ec.
have h : q %/ 2^B = 2^(D-B).
    rewrite /q (foo 2 D B); 1..2: smt(D_bound B_bound).
    rewrite mulzC. apply mulzK. by smt().
rewrite (divMr k q (2^B)) /q. 
apply (dvdz_exp2l _ _ _ B_bound).
rewrite -exprD_subz; 1..2: smt(B_bound).
rewrite ofint_hom mulzA (mulzC (2^(D-B))) -foo; 1..2: by smt(D_bound B_bound).
rewrite -ofint_hom real_mul_div ofintR.
+ apply real_neq_ltz. apply neq_ltz.
  right. apply pow2_gt0 => //. smt(D_bound).
rewrite /round. rewrite floor_add_lt1; by smt().
qed.
