From MetaRocq.Template Require Import All.
Import MRMonadNotation.

(* Unquoting evars. *)
MetaRocq Run (mlet t <- tmUnquote (tEvar fresh_evar_id []) ;; tmPrint t).
MetaRocq Run (mlet t <- tmUnquoteTyped nat (tEvar fresh_evar_id []) ;; tmPrint t).

(* Unquoting evars, with typeclass resolution. *)
Existing Class nat.
Existing Instance O.

MetaRocq Quote Definition quoted_nat := nat.
MetaRocq Run (
  mlet t <- tmUnquote (tCast (tEvar fresh_evar_id []) Cast quoted_nat) ;;
  tmEval cbv t
).
MetaRocq Run (
  mlet t <- tmUnquoteTyped nat (tEvar fresh_evar_id []) ;;
  tmEval cbv t
).