From MetaRocq.Common Require Import Universes.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qConstraintSetExtraOrdProp <: QuotationOfExtraOrdProperties ConstraintSet ConstraintSetOrdProp ConstraintSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn ConstraintSet.E ConstraintSet ConstraintSetOrdProp.P ConstraintSetExtraOrdProp.P.
    MetaRocq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraOrdProp.P").
  End qP.
  MetaRocq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "ConstraintSetExtraOrdProp").
End qConstraintSetExtraOrdProp.
