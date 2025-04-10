From Stdlib Require Import Strings.String.
From MetaRocq Require Import Template.Loader.

Inductive U : Type :=
| TT : id U.

MetaRocq Quote Recursively Definition qU := U.
