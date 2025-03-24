From MetaRocq.Template Require Import Ast.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateLookup <: QuotationOfLookup TemplateTerm Env TemplateLookup.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateLookup").
End qTemplateLookup.
