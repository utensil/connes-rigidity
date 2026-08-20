# Post-formalization audit ledger

This ledger separates technical proof acceptance from review of what the
formalization means and claims. Comparator and the Lean kernel can check a
fixed statement, proof term, and axiom boundary. They cannot decide whether
the statement is the intended theorem, whether its definitions and hypotheses
faithfully model the source mathematics, or whether claims about external
sources, provenance, and licensing are accurate.

The entries below link only to public, reproducible evidence. No entry should
be read as peer review or independent mathematical certification unless it is
explicitly marked **independent review**.

## Review states

- **Automated** means a machine check is defined and can be rerun from the
  repository.
- **Internal review** means the project has inspected and revised the material,
  but the review is not independent or peer review.
- **Independent review** is reserved for a review whose author and reasoning
  are independent of the formalization work.
- **Open** means that further review or corroboration is still planned.

An angle can have more than one state. For example, its technical interface may
be automated while its mathematical interpretation remains open.

### Internal rubric framework

The internal formalization review recorded here used the ten public
[Tau Ceti Review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/2c299e1d1950d731786005ef33209486b2fa7f9d/rubrics):
scope, correctness and faithfulness, public API, generality, naming, placement
and imports, proof quality, reuse and duplication, documentation, and
attribution. Three project-level evidence checks supplemented them: prerequisite
state, public consumer contracts, and aggregate helper/import reuse.

These thirteen angles describe an agent-run internal review method. They do
not make the review human, independent, or peer review. The planned internal
human examination using the expanded Forest notes is a separate future step.

## Supporting formalization notes

The agent-authored
[provisional formalization notes](https://utensil.github.io/forest/connes-0001/)
currently explain the overall proof architecture, Zhou's section-by-section
mathematics, the main formalization adaptations, the final assembly and trust
boundary, and the estimated work needed to formalize the EJZK input. They are
supporting exposition, not evidence that a human review has occurred.

Before an internal human review uses the notes as its guide, their coverage is
planned to expand with a theorem-by-theorem fidelity matrix, a definition and
non-vacuity consumer trace, an external-source and applicability checklist,
and an explicit review protocol. A human will then examine the expanded notes
against Zhou's paper, the cited literature, and the Lean source and record the
exact revisions, findings, limitations, and unresolved questions. That future
internal review is distinct from the independent mathematical assessment that
remains open below.

## Repaired documentation findings

The findings in this table remain part of the audit record. **Complete** means
that the specific documentation or metadata defect was repaired; it does not
close the broader mathematical-review question named in the final column.

| Finding | Status | Public evidence | Question that remains open |
| --- | --- | --- | --- |
| Machine-readable status used the repository's older metadata shape and counted the deliberate Comparator challenge hole as project proof debt. | **Complete** | [`formalization.yaml`](../formalization.yaml) now validates against schema v0.4, records zero solution sorries, and separately names the Comparator configuration, main result, axioms, literature dependency, alignment, and review boundary. | Future metadata and verifier changes remain an ongoing maintenance obligation. |
| The sole external EJZK premise was named by acronym without a full bibliographic entry in the public provenance and machine-readable result record. | **Complete** for identification | [`PROVENANCE.md`](PROVENANCE.md) gives the full EJK citation, theorem locator, and exact Lean premise boundary; [`formalization.yaml`](../formalization.yaml) records it as the main result's literature dependency. | Independent checking that the cited theorem applies to the exact formal group remains open. |
| Public status prose used a project-planning case label that could be mistaken for a mathematical case or a weaker version of Zhou's theorem. | **Complete** | The README, status, proof-hole evaluation, historical plan, Comparator description, and machine metadata now state the actual boundary: complete relative to the cited EJZK input. | The EJZK theorem itself remains an explicit premise rather than a theorem proved in this repository. |

## Current ledger

| Angle | Question | Current state | Public evidence and limitation |
| --- | --- | --- | --- |
| Proof acceptance and trust boundary | Does the frozen challenge match `Connes.theoremA`, use only the permitted axioms, and replay through the Lean kernel and nanoda inside the declared sandbox? | **Automated** | [`COMPARATOR.md`](COMPARATOR.md) describes statement comparison, Landlock and network isolation, Lean-kernel replay, and nanoda replay. This checks the encoded statement and proof term, not their mathematical fidelity. |
| Paper-to-Lean correspondence | Do Zhou's sections and headline conclusions reach identifiable Lean declarations? | **Internal review**; **open** for independent review | [`STATEMENT_MAP.md`](STATEMENT_MAP.md) gives the declaration map. [`TARGET_AUDIT.md`](TARGET_AUDIT.md) records the section-level comparison and four material target mismatches that were repaired. Independent theorem-by-theorem comparison remains open. |
| Definitions and hypotheses | Do the carriers, actions, factors, property-(T) boundary, ICC criterion, and quotient modules encode the intended objects without moving conclusions into assumptions? | **Internal review**; formal equivalence bridge **documented**; **open** for independent review | [`TARGET_AUDIT.md`](TARGET_AUDIT.md) records the concrete replacements for the identity-action, generic ICC, arbitrary non-isomorphism, and caller-supplied factor-witness scaffolds. [`STATUS.md`](STATUS.md#formal-interface-note) records the unformalized bridge between the same-universe property-(T) predicate and the standard formulation for countable groups. This is project review, not an external validation of every definition. |
| Non-vacuity and consumer use | Are the concrete witnesses used by the paper-facing endpoints and final theorem rather than merely constructed or postulated? | **Internal review**; **open** for independent review | [`STATUS.md`](STATUS.md) identifies the canonical endpoints, and [`TARGET_AUDIT.md`](TARGET_AUDIT.md) records that no free data carrying a Zhou-internal conclusion reaches the final assembly. The explicit EJZK premise remains an input. Further independent consumer and concrete-instance probes remain open. |
| External mathematics and factual claims | Is every external mathematical premise identified at its exact formal boundary, and do the cited sources support the claims made about it? | Identification **complete**; **open** for independent source and applicability review | [`STATUS.md`](STATUS.md), [`STATEMENT_MAP.md`](STATEMENT_MAP.md), [`PROVENANCE.md`](PROVENANCE.md), and [`formalization.yaml`](../formalization.yaml) identify property (T) for `EL₃(𝔽₂[t])` as the sole substantive external premise, give its EJK source and theorem locator, and distinguish it from the internal `EL₃ = SL₃` transport. Independent source-by-source verification of applicability and the mathematical claim remains open. |
| Proof architecture and public contracts | Do reusable foundations, concrete constructions, section endpoints, and final assembly have clear ownership and consumers? | **Internal review**; **open** for maintenance review | [`STATUS.md`](STATUS.md) records the current dependency architecture and canonical endpoints. Future source changes must recheck affected contracts, reuse, and dependency direction. |
| Code provenance and licensing | Can modified code be traced to public revisions and declaration blocks with the required notices? | **Internal review**; **open** as an ongoing obligation | [`PORT_MAP.md`](PORT_MAP.md) is the declaration-level transfer ledger; [`PROVENANCE.md`](PROVENANCE.md) and [`LICENSING.md`](LICENSING.md) state the source and notice policies. This does not constitute external legal advice. |
| Proof holes and external inputs | Are `sorry`, `admit`, project axioms, and theorem parameters classified without conflating them? | Inventory and classification **complete**; proof-term boundary **automated** | [`SORRY_EVAL.md`](SORRY_EVAL.md) records the source inventory, and [`formalization.yaml`](../formalization.yaml) applies the current convention of counting zero solution sorries. The Comparator challenge contains the sole intentional `sorry`; it is outside the solution dependency graph. The EJZK premise is a theorem parameter, not a project axiom or source-level proof hole. |
| Human examination using the formalization notes | Has a human checked the paper, literature, Lean declarations, and consumer paths using a review-oriented version of the explanatory notes? | **Open** | The current [provisional notes](https://utensil.github.io/forest/connes-0001/) cover the proof architecture and section-level formalization design. The fidelity, non-vacuity, source-claim, and review-protocol layers described above must be added before the planned internal human examination. |
| Independent mathematical assessment | Has a mathematically independent reviewer checked the paper correspondence, definitions, source claims, and high-risk arguments? | **Open** | No independent mathematical certification is currently claimed. The planned work is listed below. |

## Planned independent and corroborating checks

Priority should follow semantic risk rather than file size:

1. Compare Zhou's theorem, constructions, quantifiers, and hypotheses
   theorem-by-theorem with the declarations in [`STATEMENT_MAP.md`](STATEMENT_MAP.md).
2. Verify the cited EJZK result and every non-routine literature claim against
   its public source, including that the formal `EL₃(𝔽₂[t])` premise has the
   exact hypotheses needed by Zhou's argument.
3. Recheck the concrete carriers and actions for degeneracy, the three-case ICC
   split, the quotient-twist quantification, and the factor-equivalence witness
   without relying on the final theorem's successful compilation.
4. Seek independent calculations or alternate proof routes for the finite
   cocycle obstruction, orbit and square-span calculations, and the analytic
   spectral and spatial-closure bridges where practical.
5. Refresh the affected ledger rows whenever a paper-facing statement,
   definition, external source pin, code-transfer block, or trust-boundary tool
   changes.

Formalizing the EJZK theorem would remove the final external mathematical
premise. It is completion work, not by itself a post-formalization audit; the
separate audit question is whether the stated premise accurately captures and
correctly applies the cited theorem.

## Documentation roles

The audit ledger is an index, not a duplicate account of every result:

| Document | Role |
| --- | --- |
| [`STATUS.md`](STATUS.md) | Normative current scope, architecture, and trust boundary. |
| [`STATEMENT_MAP.md`](STATEMENT_MAP.md) | Paper item to canonical Lean declaration. |
| [`TARGET_AUDIT.md`](TARGET_AUDIT.md) | Detailed mathematical target and mismatch review. |
| [`SORRY_EVAL.md`](SORRY_EVAL.md) | Proof-hole, axiom, and external-input inventory. |
| [`COMPARATOR.md`](COMPARATOR.md) | Reproducible technical verification and sandbox boundary. |
| [`PORT_MAP.md`](PORT_MAP.md) | Declaration-level public code-transfer ledger. |
| [`PROVENANCE.md`](PROVENANCE.md), [`LICENSING.md`](LICENSING.md) | Source, attribution, and licensing policy. |
| [Provisional Forest notes](https://utensil.github.io/forest/connes-0001/) | Agent-authored mathematical and formalization exposition that will support, but does not replace, a later human review. |
| [`PLAN.md`](PLAN.md) | Historical planning record retained for context. |
