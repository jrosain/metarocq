From MetaRocq Require Import Template.Loader.

Axiom a_nat : nat.

MetaRocq Quote Recursively Definition qn := (a_nat + 1).

Polymorphic Axiom poly : forall x : Type, x.

MetaRocq Quote Recursively Definition qpoly := poly.

