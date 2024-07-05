require import AllCore Distr List SmtMap Dexcepted PKE_ROM StdOrder.
require (**RndExcept **) LWE FLPRG.

theory LWE_PKE_Hash.

clone import LWE as LWE_.
import Matrix.
import ZR.

type plaintext.
type ciphertext.

type raw_ciphertext = matrix * matrix.

op m_encode : plaintext -> matrix. 
op m_decode : matrix -> plaintext.

op c_encode : raw_ciphertext -> ciphertext.
op c_decode : ciphertext -> raw_ciphertext.

type pkey.
type skey.

type raw_pkey  = seed * matrix.
type raw_skey  = matrix.

op pk_encode : raw_pkey -> pkey.
op sk_encode : raw_skey -> skey.
op pk_decode : pkey -> raw_pkey.
op sk_decode : skey -> raw_skey.

axiom pk_encodeK : cancel pk_encode pk_decode.
axiom sk_encodeK : cancel sk_encode sk_decode.

(******************************************************************)
(*                The Hashed Encryption Scheme                     *)

type randomness.

op [uniform full lossless]drand : randomness distr.

op prg_kg : randomness -> seed * matrix * matrix.
op prg_kg_ideal  = 
     dlet dseed
       (fun (sd : seed) => 
          dlet (Chi_matrix n nb) (fun (s : matrix) => 
               dmap (Chi_matrix n nb) (fun (e : matrix) => (sd, s, e)))).

op prg_enc : randomness -> matrix * matrix * matrix.
op prg_enc_ideal = 
     dlet (Chi_matrix mb n)
       (fun (s' : matrix) => 
          dlet (Chi_matrix mb n) (fun (e' : matrix) => 
               dmap (Chi_matrix mb nb)  (fun (e'' : matrix) => (s', e', e'')))).

op kg(r : randomness) : pkey * skey = 
   let (sd,s,e) = prg_kg r in
   let _B =  (H sd n n) * s + e in
       (pk_encode (sd,_B),sk_encode s).

op enc(rr : randomness, pk : pkey, m : plaintext) : ciphertext = 
    let (sd,_B) = pk_decode pk in
    let (s',e',e'') = prg_enc rr in
    let _B' = s' * (H sd n n) + e' in
    let v = s' * _B + e'' in
        c_encode (_B',v + m_encode m).


op dec(sk : skey, c : ciphertext) : plaintext option =
    let (c1,c2) = c_decode c in
       Some (m_decode (c2 + -(c1 * trmx (sk_decode sk)))).

(******************************************************************)
(*    The Security Games                                          *)
clone import PKE with 
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

module LWE_PKE_HASH : Scheme = {

  proc kg() : pkey * skey = {
     var r,pk,sk;
     r <$ drand;
     (pk,sk) <- kg r;
     return (pk,sk);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
     var rr,c;
     rr <$ drand;
     c <- enc rr pk m;
     return c;
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var mo;
    mo <- dec sk c;
    return mo;
  }
}.

module LWE_PKE_HASH_PROC : Scheme = {
  proc kg(): pkey * skey = {
    var sd,s,e,t;
    sd <$ dseed;
    s  <$ Chi_matrix n nb;
    e  <$ Chi_matrix n nb;
    t  <- (H sd n n) * s + e;
    return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var sd, b,s',e',e'',b',v;
    (sd,b) <- pk_decode pk;
    s'  <$ Chi_matrix mb n;
    e' <$ Chi_matrix mb n;
    e'' <$ Chi_matrix mb nb;
    b'  <- s' * (H sd n n) + e';
    v  <- s' * b + e'';
    return c_encode (b',v + m_encode m);
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var c1,c2;
    (c1,c2) <- c_decode c;
    return (Some (m_decode (c2 + -(c1 * trmx (sk_decode sk)))));
  }
}.

clone import FLPRG as PRG_KG with
  type seed <- randomness,
  type output <- seed * matrix * matrix,
  op prg <- prg_kg,
  op dseed <- drand,
  op dout <- prg_kg_ideal
  proof *. 

clone import FLPRG as PRG_ENC with
  type seed <- randomness,
  type output <- matrix * matrix * matrix,
  op prg <- prg_enc,
  op dseed <- drand,
  op dout <- prg_enc_ideal
  proof*.

module LWE_PKE_HASH_PRG : Scheme  = {
  var sd : seed
  var s  : matrix
  var e  : matrix
  var s'  : matrix
  var e' : matrix
  var e'' : matrix

  proc kg() : pkey * skey = {
     var t;
     t <-  (H sd n n) * s + e;
     return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
     var sd,b,b',v;
     (sd,b) <- pk_decode pk;
     b' <- s' * (H sd n n) + e';
     v <- s' * b + e'';
     return c_encode (b',v + m_encode m);
  }

  include LWE_PKE_HASH [dec]
}.

module (D_KG(A : Adversary) : PRG_KG.Distinguisher)  = {
   proc distinguish(sd : seed, s : matrix, e : matrix) : bool = {
       var coins,b;
       LWE_PKE_HASH_PRG.sd <- sd;
       LWE_PKE_HASH_PRG.s <- s;
       LWE_PKE_HASH_PRG.e <- e;
       coins <$ drand;
       (LWE_PKE_HASH_PRG.s',LWE_PKE_HASH_PRG.e',LWE_PKE_HASH_PRG.e'') <- prg_enc coins;
       b <@ CPA(LWE_PKE_HASH_PRG,A).main();
       return b;
   }      
}.

module (D_ENC(A : Adversary) : PRG_ENC.Distinguisher) = {
   proc distinguish(s' : matrix, e' : matrix, e'' : matrix) : bool = {
       var b;
       (LWE_PKE_HASH_PRG.sd,LWE_PKE_HASH_PRG.s,LWE_PKE_HASH_PRG.e) <$ prg_kg_ideal;
       LWE_PKE_HASH_PRG.s' <- s';
       LWE_PKE_HASH_PRG.e' <- e';
       LWE_PKE_HASH_PRG.e'' <- e'';
       b <@ CPA(LWE_PKE_HASH_PRG,A).main();
       return b;
   }      
}.

section.
declare module A <: Adversary {-LWE_PKE_HASH_PRG}.

lemma cpa_proc &m : 
  Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res] -
   Pr[CPA(LWE_PKE_HASH_PROC,A).main() @ &m : res] = 
     Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] +
     Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ].
proof. 
have -> : Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res]  = 
  Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ].
  byequiv => //.
  proc.
  inline *.
  swap {1} 8 -4.
  by wp;call (: true);wp;rnd;call (_: true);auto => /> /#.
  
have -> : Pr[CPA(LWE_PKE_HASH_PROC, A).main() @ &m : res]   = 
        Pr[PRG_ENC.IND(PRGi, D_ENC(A)).main() @ &m : res].
+ byequiv => //.
  proc. inline *. swap {1} [11..13] -7. swap {2} 3 -1.  swap {2} 6 -4. swap {2} 4 5.
seq 0 1: #pre; 1: by auto.
seq 3 1 : (#pre /\
    (sd,s,e){1} = 
    (LWE_PKE_HASH_PRG.sd, LWE_PKE_HASH_PRG.s, LWE_PKE_HASH_PRG.e){2}). rndsem{1} 0. by auto.
seq 3 6 : (#pre /\
    (s',e',e''){1} = 
    (LWE_PKE_HASH_PRG.s', LWE_PKE_HASH_PRG.e', LWE_PKE_HASH_PRG.e''){2}). rndsem{1} 0. by auto.

  wp. call(_: true). auto. call (_: true). by auto.

have -> : Pr[PRG_KG.IND(PRG_KG.PRGi, D_KG(A)).main() @ &m : res] =
          Pr[PRG_ENC.IND(PRG_ENC.PRGr, D_ENC(A)).main() @ &m : res].
            + byequiv => //. proc;inline *. sim. swap {2} 6 -5. by auto.
by ring.
qed.

end section.

(******************************************************************)
(*       Game Hopping Security                                    *)
(******************************************************************)


(* Hop 1 *)

module LWE_PKE_HASH1 = {
  proc kg() : pkey * skey = {
    var sd,s,b;
    sd <$ dseed;
    s  <$ Chi_matrix n nb;
    b  <$ duni_matrix n nb;
    return (pk_encode (sd,b), sk_encode s);
  }

  include LWE_PKE_HASH_PROC [-kg]

}.

module B1(A : Adversary) : HAdv1_T = {

  proc guess(sd, u : matrix) : bool = {
    var pk, m0, m1, c, b, b';
    pk <- pk_encode (sd,u);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    c <@ LWE_PKE_HASH1.enc(pk, if b then m1 else m0);
    b' <@ A.guess(c);
    return b' = b;
  }
}.

section.

declare module A <: Adversary.

lemma hop1_left &m: 
  Pr[CPA(LWE_PKE_HASH_PROC,A).main() @ &m : res] =
  Pr[LWE_H1(B1(A)).main(false) @ &m : res].
proof.
byequiv => //. 
proc. inline *. 
wp. sim. wp. rnd{2}. wp. auto => /= />. rewrite duni_matrix_ll => //.
qed.

lemma hop1_right &m: 
  Pr[LWE_H1(B1(A)).main(true) @ &m : res] = 
  Pr[CPA(LWE_PKE_HASH1,A).main() @ &m : res].
proof.
byequiv => //.
proc;inline *. 
wp. sim. wp. rnd. wp. rnd{1}. rnd. wp. rnd.
auto => /= />. rewrite Chi_matrix_ll => //.
qed.

end section.

(* Hop 2 *)

module LWE_PKE_HASH2 = {

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var _A,b', v;
    _A <- H (pk_decode pk).`1;
    b' <$ duni_matrix mb n;
    v <$ duni_matrix mb nb;
    return c_encode (b',v + m_encode m);  }

  include LWE_PKE_HASH1 [-enc]

}.


module B2(A : Adversary) : HAdv2_T = {
  
  proc guess(sd : seed, _B : matrix, b'v : matrix * matrix) : bool = {
    var pk, m0, m1, c, b, m, b';
    pk <- pk_encode (sd,_B);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    m <- if b then m1 else m0;
    c <- c_encode((b'v.`1, b'v.`2 + m_encode m));
    b' <@ A.guess(c);
    return b' = b;
  }

}.

section.

declare module A <: Adversary.

lemma hop2_left &m: 
  Pr[CPA(LWE_PKE_HASH1,A).main() @ &m : res] =
  Pr[LWE_H2(B2(A)).main(false) @ &m : res].
proof.
byequiv => //.
proc. inline *. 
wp. swap {2} 11 -9. swap {2} 12 -8. swap {2} [14..16] -9.

seq 4 5 : (#pre /\ ={pk} /\ b0{1} = _B{2} /\ (pk_decode pk{2}).`1 = seed{2} /\ (pk_decode pk{2}).`2 = _B{2});
  1: by wp; rnd; rnd{1}; wp; rnd; auto; rewrite !Chi_matrix_ll => /> *; rewrite pk_encodeK => //.

  call (:true). wp. rnd{2}. wp. rnd{2}. do 2! wp. do 3! rnd. do 2! wp. rnd. call (:true). 
auto. rewrite! duni_matrix_ll => //.
qed.

lemma hop2_right &m: 
  Pr[LWE_H2(B2(A)).main(true) @ &m : res] = 
  Pr[CPA(LWE_PKE_HASH2,A).main() @ &m : res].
proof.
byequiv => //.
proc. inline *. 
swap {1} 11 -9. swap {1} 12 -8. swap{1} 8 -3. swap {1} [14..17] -9. swap {1} 16 -3. swap {1} 15 -2.

seq 5 4 : (#pre /\ ={pk} /\ _B{1} = b0{2} /\ (pk_decode pk{2}).`1 = sd{2} /\ (pk_decode pk{2}).`2 = b0{2});
  1: by wp; rnd; rnd{2}; wp; rnd; auto => />; rewrite !Chi_matrix_ll => // *; rewrite pk_encodeK => //.
wp. call (:true). wp. do 2! rnd. do 3! rnd{1}. wp. rnd. call (:true).
auto => />. rewrite !Chi_matrix_ll => //.
qed.

end section.

(* Final game analysis *)

section.

declare module A <: Adversary {-LWE_PKE_HASH_PRG}.

local module Game2(A : Adversary) = {
  proc main() = {
    var sd, _B, m0, m1, m, _B', v, c, b, b';
    sd <$ dseed;
    _B <$ duni_matrix n nb;
    (m0, m1) <@ A.choose(pk_encode (sd,_B));
    b <$ {0,1};
    m <- if b then m1 else m0;

    _B' <$ duni_matrix mb n;
    v <$ duni_matrix mb nb;
    c <- c_encode(_B', v);
    b' <@ A.guess(c);
    return b = b';
  }
}.

local lemma game2_equiv &m :
  Pr[CPA(LWE_PKE_HASH2,A).main() @ &m : res] = 
  Pr[Game2(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
call(_: true). wp.
rnd (fun z, z + m_encode m{2})
    (fun z, z - m_encode m{2}).
rnd. wp. rnd. call(_:true). wp. rnd. rnd{1}. rnd.
auto => /> *. rewrite Chi_matrix_ll => /> ? ? ? ? result_R bL *.
split => vR *. rewrite -addmA addNm eq_sym. apply lin_addm0. 
auto => /> *; split => *; [ ring | split => *; [ring | smt()]].
qed.

local lemma game2_prob &m :
  islossless A.guess => islossless A.choose =>
  Pr[Game2(A).main() @ &m : res] = 1%r / 2%r.
proof.
move => A_guess_ll A_choose_ll.
byphoare => //. 
proc.
rnd  (pred1 b')=> //=.
conseq (: _ ==> true).
+ by move=> />; apply DBool.dbool1E.
by islossless; smt(duni_ll dshort_ll). 
qed.

lemma main_theorem &m :
  islossless A.guess => islossless A.choose =>
  `| Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res] -  1%r / 2%r | <=
    `| Pr[LWE_H(B1(A)).main(false,false) @ &m : res] -
       Pr[LWE_H(B1(A)).main(false,true) @ &m : res] | + 
    `| Pr[LWE_H(B2(A)).main(true,false) @ &m : res] -
       Pr[LWE_H(B2(A)).main(true,true) @ &m : res] | +
    `| Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] | +
    `| Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ] |.
proof.
move => A_guess_ll A_choose_ll.
have := (cpa_proc A &m).
rewrite (hop1_left A &m).
rewrite (hop1_right A &m).
rewrite (hop2_left A &m).
rewrite (hop2_right A &m).
rewrite (game2_equiv &m).
rewrite (game2_prob &m _ _) //.
by smt().
qed.

end section.
