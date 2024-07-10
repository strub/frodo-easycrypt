(* -------------------------------------------------------------------- *)
require import AllCore IntDiv Real.
(*---*) import RField.

(* -------------------------------------------------------------------- *)
op round (x: real): int = floor (x + inv 2%r).

(* -------------------------------------------------------------------- *)
lemma floor_add_lt1 x y: 0%r <= y < 1%r => floor (x%r + y) = x.
proof. by move=> rg; rewrite floorP /#. qed.

lemma round_fromint x : round x%r = x.
proof. by rewrite /round floor_add_lt1 /#. qed.

(* -------------------------------------------------------------------- *)
op D: {int | 0 <= D <= 16} as D_bound.
op B: {int | 0 <= B <= D} as B_bound.

(* -------------------------------------------------------------------- *)
hint exact : D_bound B_bound.

(* -------------------------------------------------------------------- *)
op q = 2^D.

lemma nz_q : q <> 0.
proof. by rewrite expf_eq0. qed.

hint exact : nz_q.

(* -------------------------------------------------------------------- *)
(* 0 <= k < 2^B. *)
op ec (k : int) = k * q %/ 2^B. 
op dc (c : int) = round (c%r * (2^B)%r / q%r) %% 2^B.

(* -------------------------------------------------------------------- *)
lemma decode_correctness k: 0 <= k < (2^B) => dc (ec k) = k.
proof.
move=> [# ge0_k ltk] @/dc @/ec @/q.
have dvd_2XB_2XD: 2^B %| 2^D by apply/dvdz_exp2l/B_bound.
rewrite divMr // -fromintM -mulrA divzK // fromintM //.
rewrite mulrK; first by rewrite eq_fromint expf_eq0.
by rewrite round_fromint pmod_small.
qed.
