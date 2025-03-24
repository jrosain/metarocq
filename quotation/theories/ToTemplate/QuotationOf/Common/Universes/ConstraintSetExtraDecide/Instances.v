From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.

Module qConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide ConstraintSet.E ConstraintSet ConstraintSetExtraDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraDecide").
End qConstraintSetExtraDecide.
