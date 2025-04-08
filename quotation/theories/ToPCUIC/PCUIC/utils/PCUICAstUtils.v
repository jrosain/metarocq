From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init.
From MetaRocq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst.

#[export] Instance quote_mkApps_spec {f args fargs1 args2 fargs} : ground_quotable (@mkApps_spec f args fargs1 args2 fargs) := ltac:(destruct 1; exact _).
(*
#[export] Instance quote_tCaseBrsType {A P l} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, ground_quotable (P x)} : ground_quotable (@tCaseBrsType A P l) := _.
#[export] Instance quote_tFixType {A P P' m} {qA : quotation_of A} {qP : quotation_of P} {qP' : quotation_of P'} {quoteA : ground_quotable A} {quoteP : forall x, ground_quotable (P x)} {quoteP' : forall x, ground_quotable (P' x)} : ground_quotable (@tFixType A P P' m) := _.
*)
