From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Stdlib.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevel <: QuotationOfOrderedType Level.
  MetaRocq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 everything (*None*) "Level").
End qLevel.
