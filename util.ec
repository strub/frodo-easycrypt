require import AllCore List.
from Jasmin require import JWord.
require import BitEncoding.
(*---*) import BitChunking.

op concatMap (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).
op splitAt n (xs: 'a list): ('a list * 'a list) = (take n xs, drop n xs).
op mapT (f1: 'a -> 'b) (f2: 'c -> 'd) (x: ('a * 'c)): ('b * 'd) = (f1 x.`1, f2 x.`2).

op tobytes (xs: bool list): W8.t list = map W8.bits2w (chunk W8.size xs).

op w8ltoW16l (xs: W8.t list): W16.t list = map W16.bits2w (chunk W16.size (concatMap W8.w2bits xs)).

op w8ltoW128(xs: W8.t list): W128.t = W128.bits2w (concatMap W8.w2bits xs).
op w8ltoW256(xs: W8.t list): W256.t = W256.bits2w (concatMap W8.w2bits xs).
op w128toW8l (x: W128.t): W8.t list = map W8.bits2w (chunk W8.size (W128.w2bits x)).
op w256toW8l (x: W256.t): W8.t list = map W8.bits2w (chunk W8.size (W256.w2bits x)).
