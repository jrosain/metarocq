From MetaRocq Require Import Template.All.
Require Export List.
Open Scope bs_scope.
MetaRocq Run (tmLemma "test" (@nil nat = @nil nat)).
