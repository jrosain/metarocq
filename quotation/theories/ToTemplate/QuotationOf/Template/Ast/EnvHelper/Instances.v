From MetaRocq.Template Require Import Ast.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.Common Require Import Environment.

Module QuoteEnvHelper <: QuoteEnvironmentHelperSig TemplateTerm Env := QuoteEnvironmentHelper TemplateTerm Env.

Module qQuoteEnvHelper <: QuotationOfQuoteEnvironmentHelper TemplateTerm Env QuoteEnvHelper.
  MetaRocq Run (tmMakeQuotationOfModule everything None "QuoteEnvHelper").
End qQuoteEnvHelper.
