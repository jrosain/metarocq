From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateDeclarationTyping <: QuotationOfDeclarationTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateConversionPar TemplateTyping TemplateLookup TemplateGlobalMaps TemplateDeclarationTyping.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateDeclarationTyping").
End qTemplateDeclarationTyping.
