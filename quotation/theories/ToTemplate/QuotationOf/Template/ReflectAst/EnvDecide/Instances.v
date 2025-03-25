From MetaRocq.Template Require Import Ast ReflectAst.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qEnvDecide <: QuotationOfEnvironmentDecide TemplateTerm Env EnvDecide.
  MetaRocq Run (tmMakeQuotationOfModule everything None "EnvDecide").
End qEnvDecide.
