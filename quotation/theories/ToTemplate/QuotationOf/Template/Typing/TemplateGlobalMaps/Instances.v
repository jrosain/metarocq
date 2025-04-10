From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateGlobalMaps <: QuotationOfGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateGlobalMaps.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateGlobalMaps").
End qTemplateGlobalMaps.
