From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateEnvTyping <: QuotationOfEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateEnvTyping").
End qTemplateEnvTyping.
