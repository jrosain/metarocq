From MetaRocq Require Import Template.Loader.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
MetaRocq Quote Recursively Definition qII := II.
