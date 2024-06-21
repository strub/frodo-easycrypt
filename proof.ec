require import AllCore Distr List SmtMap Dexcepted PKE_ROM StdOrder.
require (**RndExcept **) MLWE.

theory MLWE_PKE_Hash.

clone import MLWE as MLWE_.
import Matrix_.
import ZR.

import StdOrder.IntOrder Matrix_ Big.BAdd.

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

op prg_enc : randomness -> matrix * matrix * matrix.

op kg(r : randomness) : pkey * skey = 
   let (sd,s,e) = prg_kg r in
   let t =  (H sd) * s + e in
       (pk_encode (sd,t),sk_encode s).

op enc(rr : randomness, pk : pkey, m : plaintext) : ciphertext = 
    let (sd,b) = pk_decode pk in
    let (s',e',e'') = prg_enc rr in
    let b' = s' * (H sd) + e' in
    let v = s' * b + e'' in
        c_encode (b',v + m_encode m).

op dec(sk : skey, c : ciphertext) : plaintext option =
    let (c1,c2) = c_decode c in
       Some (m_decode (c2 + -(c1 * m_transpose (sk_decode sk)))).

(******************************************************************)
(*    The Security Games                                          *)
clone import PKE with 
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

module DLWE_PKE_HASH : Scheme = {

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

module DLWE_PKE_HASH_PROC : Scheme = {
  proc kg(): pkey * skey = {
    var sd,s,e,t;
    sd <$ dseed;
    s  <$ dshort_matrix;
    e  <$ dshort_matrix;
    t  <- (H sd) * s + e;
    return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var sd, b,s',e',e'',b',v;
    (sd,b) <- pk_decode pk;
    s'  <$ dshort_matrix;
    e' <$ dshort_matrix;
    e'' <$ dshort_matrix;
    b'  <- s' * (H sd) + e';
    v  <- s' * b + e'';
    return c_encode (b',v + m_encode m);
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var c1,c2;
    (c1,c2) <- c_decode c;
    return (Some (m_decode (c2 + -(c1 * m_transpose (sk_decode sk)))));
  }
}.


print DLWE_PKE_HASH_PROC.
print MLWE_H.
