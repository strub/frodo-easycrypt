require import AllCore Int Real List IntDiv.
from Jasmin require import JWord.

type publickey = PKE.seedA * W8.t list.
type secretkey = W128.t * publickey * PKE.skey * W128.t.
type ciphertext = W8.t list * W8.t list * W256.t.
type sharedsecret = W128.t.

module FrodoKEM = {
  proc kg_derand(coins: W128.t * W256.t * W128.t): publickey * secretkey = {
    var s, seedSE, z, seedA;
    var _pk, pk, sk;
    var b, matb;
    var pkh;

    (s, seedSE, z) <- coins;

    seedA <- w8ltoW128 (SHAKE128 (w128toW8l z) 16);
    (_pk, sk) <@ PKE.PKE.kg_derand((seedA,seedSE));
    (seedA, matb) <- _pk;
    b <@ Encoding.pack(matb, N, Nb);
    pkh <- w8ltoW128 (SHAKE128 (tobytes (W128.w2bits seedA ++ b)) 16);

    pk <- (seedA, tobytes b);

    return (pk, (s, pk, sk, pkh));
  }

  proc end_derand(pk: publickey, coins: W128.t * W256.t): ciphertext * sharedsecret = {
    var u, pkh, k: W128.t;
    var salt, seedSE: W256.t;
    var _b, mc1, mc2: M.t;
    var _c1, _c2: bool list;
    var ss: W128.t;

    (u, salt) <- coins;
    pkh <- w8ltoW128 (SHAKE128 (w128toW8l pk.`1 ++ pk.`2) 16);
    _b <@ Encoding.unpack(concatMap W8.w2bits pk.`2, N, Nb);

    (seedSE, k) <- mapT w8ltoW256 w8ltoW128
      (splitAt 32 (SHAKE128 (w128toW8l pkh ++ w128toW8l u ++ w256toW8l salt) 48));

    (mc1, mc2) <@ PKE.PKE.enc_derand(u, (pk.`1, _b), seedSE);
    _c1 <@ Encoding.pack (mc1, Nb, N);
    _c2 <@ Encoding.pack (mc2, Nb, Nb);

    ss <- w8ltoW128 (SHAKE128 (tobytes (_c1 ++ _c2) ++ w256toW8l salt ++ w128toW8l k) 16);

    return ((tobytes _c1, tobytes _c2, salt), ss);
  }

  proc dec(ct: ciphertext, sk: secretkey): sharedsecret = {
    var pk;
    var c1, c2, salt;
    var s, seedA, b, st, pkh;
    var mb', mc: M.t;
    var u';
    var seedSE', k';
    var r;
    var ms', me', me'', mb, mb'', ma, mv: M.t;
    var mu, mc': M.t;
    var ss;

    (s, pk, st, pkh) <- sk;
    (seedA, b) <- pk;
    (c1, c2, salt) <- ct;
    mb' <@ Encoding.unpack(concatMap W8.w2bits c1, Nb, N);
    mc <@ Encoding.unpack(concatMap W8.w2bits c2, Nb, Nb);

    u' <@ PKE.PKE.dec((mb',mc), st);

    (seedSE', k') <- mapT w8ltoW256 w8ltoW128
      (splitAt 32 (SHAKE128 (w128toW8l pkh ++ w128toW8l u' ++ w256toW8l salt) 48));

    r <- w8ltoW16l (SHAKE128 (mask96 :: w256toW8l seedSE') (4*N*Nb + 2*Nb*Nb));

    ms' <@ Sample.matrix(mkarray (take (N*Nb) r), Nb, N);
    me' <@ Sample.matrix(mkarray (take (N*Nb) (drop (N*Nb) r)), Nb, N);
    ma <@ GenA.init(seedA);

    mb'' <- ms' * ma + me';
    me'' <@ Sample.matrix(mkarray (take (Nb*Nb) (drop (2*N*Nb) r)), Nb, Nb);

    mb <@ Encoding.unpack(concatMap W8.w2bits b, N, Nb);
    mv <- ms'*mb + me'';

    mu <@ Encoding.encode(mkarray (W128.w2bits u'));
    mc' <- mv + mu;

    if (mb' <> mb'' && mc <> mc') {
       k' <- s;
    }

    ss <- w8ltoW128 (SHAKE128 (c1 ++ c2 ++ w256toW8l salt ++ w128toW8l k') 16);
    return ss;
  }
}.

print FrodoKEM.


