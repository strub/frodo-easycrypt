require import AllCore Int Real List IntDiv.
from Jasmin require import JWord.

type publickey = PKE.pkey.
type secretkey = W128.t * publickey * PKE.skey * W128.t.
type ciphertext = PKE.ciphertext * W256.t.
type sharedsecret = W128.t.

op G1 (pk: publickey): W128.t = w8ltoW128 (SHAKE128 (w128toW8l pk.`1 ++ ArrayPNNb.to_list pk.`2) 16).
op H_z (z: W128.t): W128.t = w8ltoW128 (SHAKE128 (w128toW8l z) 16).
op G2 (pkh: W128.t) (coins: W128.t * W256.t): (W256.t * W128.t) =
    mapT w8ltoW256 w8ltoW128
      (splitAt 32 (SHAKE128 (w128toW8l pkh ++ w128toW8l coins.`1 ++ w256toW8l coins.`2) 48)).

op F (ct: PKE.ciphertext) (salt: W256.t) (k: W128.t): sharedsecret =
    w8ltoW128 (SHAKE128 (ArrayPNbN.to_list ct.`1 ++ ArrayPNbNb.to_list ct.`2 ++ w256toW8l salt ++ w128toW8l k) 16).

module FrodoKEM = {
  proc kg_derand(coins: W128.t * W256.t * W128.t): publickey * secretkey = {
    var s, seedSE, z, seedA;
    var pk, sk;
    var pkh;

    (s, seedSE, z) <- coins;

    seedA <- H_z z;
    (pk, sk) <@ PKE.PKE.kg_derand((seedA,seedSE));
    pkh <- G1 pk;

    return (pk, (s, pk, sk, pkh));
  }

  proc end_derand(pk: publickey, coins: W128.t * W256.t): ciphertext * sharedsecret = {
    var u, pkh, k: W128.t;
    var salt, seedSE: W256.t;
    var _b, mc1, mc2: M.t;
    var ct;
    var ss: W128.t;

    (u, salt) <- coins;
    pkh <- G1 pk;
    (seedSE, k) <- G2 pkh coins;
    ct <@ PKE.PKE.enc_derand(u, pk, seedSE);
    ss <- F ct salt k;

    return ((ct, salt), ss);
  }

  proc dec(ct: ciphertext, sk: secretkey): sharedsecret = {
    var s, pk, st, pkh;
    var u', ct1, ct2, salt;
    var seedSE', k';
    var ss;

    (s, pk, st, pkh) <- sk;
    (ct1, salt) <- ct;

    u' <@ PKE.PKE.dec(ct1, st);
    (seedSE', k') <- G2 pkh (u', salt);

    ct2 <@ PKE.PKE.enc_derand(u', pk, seedSE');

    if (ct1 <> ct2) {
       k' <- s;
    }

    ss <- F ct1 salt k';
    return ss;
  }
}.

print FrodoKEM.


