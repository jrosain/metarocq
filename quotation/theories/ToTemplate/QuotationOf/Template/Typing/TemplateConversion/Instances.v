From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateConversion <: QuotationOfConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateConversion").
End qTemplateConversion.
