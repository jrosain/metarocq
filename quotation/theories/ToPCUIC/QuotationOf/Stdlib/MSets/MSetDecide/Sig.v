From Stdlib.MSets Require Import MSetInterface MSetDecide.
From MetaRocq.Utils Require Import MCMSets.
From MetaRocq.Quotation.ToPCUIC Require Import Init.

Module Export MSets.
  Module Type QuotationOfWDecideOn (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWDecideOn.

  Module Type QuotationOfWDecide (M : WSets) (F : WDecideSig M) := QuotationOfWDecideOn M.E M F.
End MSets.
