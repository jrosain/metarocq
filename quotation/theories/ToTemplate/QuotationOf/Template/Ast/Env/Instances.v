From MetaRocq.Template Require Import Ast.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qEnv <: QuotationOfEnvironment TemplateTerm Env.
  MetaRocq Run (tmMakeQuotationOfModule everything None "Env").
End qEnv.
