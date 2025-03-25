From MetaRocq Require Import Template.Loader.
From Stdlib Require Import Uint63.

Definition n : Uint63.int := 42.
Import List.ListNotations.
Definition ns : list Uint63.int := [n]%list.


MetaRocq Quote Recursively Definition q_n := n.
MetaRocq Unquote Definition n' := (snd q_n).

MetaRocq Quote Recursively Definition q_ns := ns.
MetaRocq Unquote Definition ns' := (snd q_ns).

