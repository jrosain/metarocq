From Stdlib.MSets Require Import MSetFacts.
From MetaRocq.Utils Require Import MRMSets.
From MetaRocq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module Type QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    MetaRocq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFactsOn.

  Module Type QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.
End MSets.
