(* See PR #1109. *)

From MetaRocq.Template Require Import All.
From Stdlib Require Import PrimString.

MetaRocq Quote Definition quote_test := "quote_me"%pstring.
MetaRocq Unquote Definition unquote_test := (tString "unquote_me"%pstring).

