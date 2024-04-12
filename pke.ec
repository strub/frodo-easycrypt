require import AllCore Int Real List IntDiv.
require DynMatrix.
require import ZModP.
require BitWord.
require import Array.
require import Keccak1600_Spec.
require import BitEncoding.
(*---*) import BS2Int.
(*---*) import BitChunking.

from Jasmin require import JWord.
from Jasmin require import JArray.

op q: int = 32768 axiomatized by qE.
op N: int = 640 axiomatized by nE.
op Nb: int = 8 axiomatized by nbE.
op D: int = 15 axiomatized by dE.
op B: int = 2 axiomatized by bE.
op Lsec: int = 24 axiomatized by lsecE.

clone import ZModRing as Zq with
  op p <- q
  rename "zmod" as "Zq"
  proof ge2_p by rewrite qE //.

theory M.
clone include DynMatrix with
  theory ZR <- ZModpRing
  proof *.

type t = Matrices.matrix.
op size: { int*int | 0 <= size.`1 && 0 <= size.`2 } as ge0_size.
axiom size_eq (m: t): size m = size. 

op "_.[_<-_]" (m: t) (ij: int*int) (v: R): t.
op tolist (m: t): R list =
  let ys = range 0 (cols m) in
  let xs = range 0 (rows m) in
  let ms = concatMap (fun x => map (fun y => (x, y)) ys) xs in
  map (fun i => m.[i] ) ms.

end M.

(*---*) import M.

abbrev mask5f = W8.of_int 95 (* 95 = 0x5f *).
abbrev mask96 = W8.of_int 150 (* 150 = 0x96 *).

op CDF_table: int array = mkarray [
   4643; 13363; 20579; 25843;
   29227; 31145; 32103; 32525;
   32689; 32745; 32762; 32766;
   32767

].

module Sample = {
  proc sample(r: bool list): Zq = {
    var i, e, t;
    e <- 0;
    i <- 0;
    t <- bs2int (behead r);

    while (i < size CDF_table) {
      if (CDF_table.[i] < t) {
        e <- e + 1;
      }
      i <- i + 1;
    }

    e <- (-1)^(b2i (head false r)) * e;
    return inZq e;
  }

  proc matrix(r: W16.t array, n1: int, n2: int): M.t = {
      var i, j, x;
      var m: M.t;
      i <- 0;
      j <- 0;
      while (i < n1) {
        while (j < n2) {
          x <@ sample(W16.w2bits (r.[i * n2 + j]));
          m.[(i,j)] <- x;
          n2 <- n2 + 1;
        }
        n1 <- n1 + 1;
      }

      return m;
  }
}.

module Encoding = {
  proc pack(c: M.t, n1: int, n2: int): bool list = {
    var i, j, l, cd;
    var b: bool array;
    i <- 0;

    while (i < n1) {
      j <- 0;

      while (j < n2) {
        cd <- mkarray (take D (int2bs 16 (asint c.[(i,j)])));

        l <- 0;
        while (l < D) {
          b.[(i*n2+j)*D+l] <- cd.[D-1-l];

          l <- l + 1;
        }

        j <- j + 1;
      }
      i <- i + 1;
    }

    return ofarray b;
  }

  proc unpack(bs: bool list, n1: int, n2: int):  M.t = {
    var i, j, l, ac;
    var arrb: bool array;
    var c: M.t;

    arrb <- mkarray bs;

    i <- 0;
    while (i < n1) {
      j <- 0;

      while (j < n2) {
        l <- 0;
        ac <- 0;

        while (l < D) {
          ac <- ac + (b2i arrb.[(i*n2+j)*D+l]) * 2^(D-1-l);
          l <- l + 1;
        }
        c.[(i, j)] <- inZq ac;

        j <- j + 1;
      }
      i <- i + 1;
    }

    return c;
  }

  proc encode(bk: bool array): M.t = {
    var i, j, l;
    var k;
    var mk: M.t;

    i <- 0;
    while (i < Nb) {
      j <- 0;
      while (j < Nb) {
        l <- 0;
        while (l < B) {
          k <- k + (b2i bk.[(i*Nb+j)*B + l]) * 2^l;
          l <- l + 1;
        }

        mk.[(i, j)] <- inZq (k * q %/ (2^B));

        j <- j + 1;
      }
      i <- i + 1;
    }

    return mk;
  }

  proc decode(mk: M.t): bool array = {
    var i, j, l;
    var k;
    var bk: bool array;

    i <- 0;
    while (i < Nb) {
      j <- 0;

      while (j < Nb) {
        k <- mkarray (int2bs B (floor ((asint mk.[(i,j)] * 2^B)%r / q%r + 1%r/2%r) %% 2^B));

        l <- 0;
        while (l < B) {
          bk.[(i * Nb + j)*B + l] <- k.[l];
          l <- l + 1;
        }

        j <- j + 1;
      }
      i <- i + 1;
    }

    return bk;
  }
}.

module GenA = {
  proc init(seedA: W128.t): M.t = {
    var i, j;
    var seed: W8.t list;
    var c: W16.t array;
    var a: M.t;

    i <- 0;
    while (i < N) {
      seed <- tobytes (int2bs 16 i) ++ w128toW8l seedA;
      c <- mkarray (w8ltoW16l (SHAKE128 seed (2*N)));

      j <- 0;
      while (j < N) {
        a.[(i,j)] <- inZq (W16.to_uint c.[j]);
        j <- j+1;
      }

      i <- i+1;
    }

    return a;
  }
}.

clone export PolyArray as ArrayPNNb  with op size <- D*N*Nb%/8.
clone export PolyArray as ArrayPNbN  with op size <- D*Nb*N%/8.
clone export PolyArray as ArrayPNbNb  with op size <- D*Nb*Nb%/8.
print ArrayPNNb.

theory PKE.
type seedA = W128.t.
(* (n,nb) *)
type B = M.t.

type pkey = W128.t * W8.t ArrayPNNb.t.
(* (nb,n) *)
type skey = M.t.

type ciphertext = W8.t ArrayPNbN.t * W8.t ArrayPNbNb.t.
type plaintext = W128.t.


module PKE = {
  proc kg_derand(coins: W128.t * W256.t) : pkey * skey = {
    var ma, mb, me, mst: M.t; (* a: (n, n), b, e: (n, nb), st: (nb, n) *)
    var seedA: W128.t;
    var seedSE: W256.t;
    var r: W16.t list;
    var b: bool list;

    seedA <- coins.`1;
    seedSE <- coins.`2;

    ma <@ GenA.init(seedA);

    r <- w8ltoW16l (SHAKE128 (mask5f :: w256toW8l seedSE) (4*N*Nb));
    mst <@ Sample.matrix(mkarray (take (N*Nb) r), Nb, N);
    me <@ Sample.matrix(mkarray (drop (N*Nb) r), N, Nb);

    mb <- ma * (trmx mst) + me;
    b <@ Encoding.pack(mb, N, Nb);

    return ((seedA, ArrayPNNb.of_list witness (tobytes b)), mst);
  }

  proc enc_derand(pt: plaintext, pk: pkey, coins: W256.t): ciphertext = {
    var ma, mb, ms', me', me'', mb', mu, mv, mc: M.t;
    var c1, c2;
    var seedA, b;
    var r: W16.t list;

    (seedA, b) <- pk;
    ma <@ GenA.init(seedA);
    mb <@ Encoding.unpack(concatMap W8.w2bits (ArrayPNNb.to_list b), N, Nb);

    r <- w8ltoW16l (SHAKE128 (mask96 :: w256toW8l coins) (4*N*Nb + 2*Nb*Nb));
    ms' <@ Sample.matrix(mkarray (take (N*Nb) r), Nb, N);
    me' <@ Sample.matrix(mkarray (take (N*Nb) (drop (N*Nb) r)), Nb, N);
    me'' <@ Sample.matrix(mkarray (drop (2*N*Nb) r), Nb, Nb);

    mb' <- ms' * ma + me';
    c1 <@ Encoding.pack(mb', Nb, N);

    mu <@ Encoding.encode(mkarray (W128.w2bits pt));
    mv <- ms' * mb + me'';
    mc <- mv + mu;
    c2 <@ Encoding.pack(mc, Nb, Nb);

    return (ArrayPNbN.of_list witness (tobytes c1), ArrayPNbNb.of_list witness (tobytes c2));
  }

  proc dec(ct: ciphertext, sk: skey): plaintext = {
    var c1, c2;
    var mb', mc, m: M.t; (* c1: (nb, n), c2: (nb, nb) *)
    var u;

    (c1, c2) <- ct;
    mb' <@ Encoding.unpack(concatMap W8.w2bits (ArrayPNbN.to_list c1), Nb, N);
    mc <@ Encoding.unpack(concatMap W8.w2bits (ArrayPNbNb.to_list c2), Nb, Nb);
    m <- mc - mb' * (trmx sk);

    u <@ Encoding.decode(m);

    return W128.bits2w (ofarray u);
  }
}.
end PKE.

print PKE.
