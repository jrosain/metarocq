From MetaRocq Require Import Template.Loader.
From Stdlib Require Import Streams.

CoFixpoint ones := Cons 1 ones.

MetaRocq Quote Recursively Definition q_ones := ones.

