# AI disclosure

## In the paper

*The paper's statement on the use of artificial intelligence, reproduced as it appears there
(`paper/mosaic-spaces.tex`, section "Use of artificial intelligence"):*

> Artificial intelligence was used extensively in the preparation of this work. Claude Fable 5.2
> and ChatGPT Astra assisted in the development of the reported results, proof writing,
> proofreading, literature searches, revision, and mathematical checking, including attempts to
> identify errors and gaps. These contributions extended beyond language editing: the
> constructions and arguments presented here, the identification of the relevant published
> sources, and the critical review of earlier drafts were all obtained with substantial assistance
> from these systems. Automated checks are not independent human peer review or machine-checked
> formal verification, and no such review or verification of this article is claimed.

The last sentence was written before the Lean formalization existed. The paper itself does not
describe the formalization; the formalization is described below and in [`lean/`](lean/).

## The Lean formalization

All Lean code in [`lean/`](lean/), statements and proofs, was written by AI systems at the
author's request: Claude Fable 5.2 prepared the coverage ledger, the documentation and the first
Section 2 modules; Claude Opus 5.5 wrote the rest (sessions of 16, 17 and 20 November 2026). The
author supplied the article and the brief in [`prompt/first-prompt.md`](prompt/first-prompt.md)
and directed the scope; the examples of the article were excluded at his request.

The statements were reviewed by separate Claude agents (an adversarial reviewer, a sceptic and a
referee, each with a fresh context and a read-only snapshot);
[`lean/reports/ai_adversarial_review.md`](lean/reports/ai_adversarial_review.md) records their
findings and the responses. These are AI reviews. **No human has yet compared the Lean
statements with the paper, and no independent expert has verified the proofs of the paper.**
