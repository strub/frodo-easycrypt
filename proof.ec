require import AllCore Distr List SmtMap Dexcepted PKE_ROM StdOrder.
require (**RndExcept **) LWE FLPRG.

theory MLWE_PKE_Hash.

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

module MLWE_PKE_HASH : Scheme = {

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

module MLWE_PKE_HASH_PROC : Scheme = {
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

module MLWE_PKE_HASH_PRG : Scheme  = {
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

  include MLWE_PKE_HASH [dec]
}.

module (D_KG(A : Adversary) : PRG_KG.Distinguisher)  = {
   proc distinguish(sd : seed, s : matrix, e : matrix) : bool = {
       var coins,b;
       MLWE_PKE_HASH_PRG.sd <- sd;
       MLWE_PKE_HASH_PRG.s <- s;
       MLWE_PKE_HASH_PRG.e <- e;
       coins <$ drand;
       (MLWE_PKE_HASH_PRG.s',MLWE_PKE_HASH_PRG.e',MLWE_PKE_HASH_PRG.e'') <- prg_enc coins;
       b <@ CPA(MLWE_PKE_HASH_PRG,A).main();
       return b;
   }      
}.

module (D_ENC(A : Adversary) : PRG_ENC.Distinguisher) = {
   proc distinguish(s' : matrix, e' : matrix, e'' : matrix) : bool = {
       var b;
       (MLWE_PKE_HASH_PRG.sd,MLWE_PKE_HASH_PRG.s,MLWE_PKE_HASH_PRG.e) <$ prg_kg_ideal;
       MLWE_PKE_HASH_PRG.s' <- s';
       MLWE_PKE_HASH_PRG.e' <- e';
       MLWE_PKE_HASH_PRG.e'' <- e'';
       b <@ CPA(MLWE_PKE_HASH_PRG,A).main();
       return b;
   }      
}.

section.
declare module A <: Adversary {-MLWE_PKE_HASH_PRG}.

lemma cpa_proc &m : 
  Pr[CPA(MLWE_PKE_HASH,A).main() @ &m : res] -
   Pr[CPA(MLWE_PKE_HASH_PROC,A).main() @ &m : res] = 
     Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] +
     Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ].
proof. 
have -> : Pr[CPA(MLWE_PKE_HASH,A).main() @ &m : res]  = 
  Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ].
  byequiv => //.
  proc.
  inline *.
  swap {1} 8 -4.
  by wp;call (: true);wp;rnd;call (_: true);auto => /> /#.
  
have -> : Pr[CPA(MLWE_PKE_HASH_PROC, A).main() @ &m : res]   = 
        Pr[PRG_ENC.IND(PRGi, D_ENC(A)).main() @ &m : res].
+ byequiv => //.
  proc. inline *. swap {1} [11..13] -7. swap {2} 3 -1.  swap {2} 6 -4. swap {2} 4 5.
seq 0 1: #pre; 1: by auto.
seq 3 1 : (#pre /\
    (sd,s,e){1} = 
    (MLWE_PKE_HASH_PRG.sd, MLWE_PKE_HASH_PRG.s, MLWE_PKE_HASH_PRG.e){2}). rndsem{1} 0. by auto.
seq 3 6 : (#pre /\
    (s',e',e''){1} = 
    (MLWE_PKE_HASH_PRG.s', MLWE_PKE_HASH_PRG.e', MLWE_PKE_HASH_PRG.e''){2}). rndsem{1} 0. by auto.

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
    b  <$ Chi_matrix n nb;
    return (pk_encode (sd,b), sk_encode s);
  }

  include MLWE_PKE_HASH_PROC [-kg]

}.

module B1(A : Adversary) : HAdv_T = {

  proc kg(sd : seed, b : matrix) : pkey * skey = {
    return (pk_encode (sd,b), witness);
  }
  
  proc guess(sd, _B : matrix) : bool = {
    var pk, sk, m0, m1, c, b, b';
    (pk,sk) <@ kg(sd,_B);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    c <@ LWE_PKE_HASH1.enc(pk, if b then m1 else m0);
    b' <@ A.guess(c);
    return b' = b;
  }
}.
