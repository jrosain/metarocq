From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MCMonadNotation.

MetaRocq Test Quote negb.
MetaRocq Run (tmBind (tmEval (unfold (MPfile ["Datatypes"; "Init"; "Corelib"], "negb")) negb) tmPrint).
