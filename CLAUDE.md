# CLAUDE.md

Lean 4 guidelines for formalizing statements, creating definitions, and proving theorems.

This file is the single source of truth for Lean workflow behavior in this project.

Tradeoff: these guidelines bias toward proof reliability over speed.

## MCP Self-Check (Default)

Do not rely on user-provided flags as the primary signal.

At the start of each Lean task, Claude should explicitly self-check MCP availability and report one of:
- Lean MCP is available in this session.
- Lean MCP is not available in this session.

If MCP is available:
- Prefer querying symbols/types/goals via Lean LSP MCP before proposing edits.
- Do not invent theorem names when a lookup can confirm them.

If MCP is not available:
- State that limitation once.
- Continue with best-effort Lean/Mathlib reasoning and call out uncertain names.

## 1. Clarify The Statement First

Before proving:
- Restate the theorem in precise Lean terms.
- If multiple formalizations are plausible, choose the most general.

## 2. Reuse Existing Library First

Before adding new declarations:
- Search for existing Mathlib definitions and lemmas. Use `exact?`, `apply?`, `rw?`, or Loogle/LeanSearch if MCP is available.
- Prefer existing notation and canonical names.
- Add new definitions only when no existing one fits.

Test: if a new definition duplicates a known concept, stop and reuse.

## 3. Do Not Hallucinate Lemma Names

Never invent a Mathlib lemma or theorem name from memory. LLMs confidently produce names like `Nat.add_comm_of_le` or `List.filter_length_le` that do not exist.

- If MCP is available, query it before referencing any Mathlib name.
- Prefer search tactics over hardcoded names when uncertain.
- Guess as a last resort.

## 4. Verify Imports and References Exist

Every import you write must correspond to a real Mathlib or project module. Every lemma, definition, or tactic you reference must actually exist at the version of Lean/Mathlib the project uses.

- Do not assume an import path is valid because it looks plausible.
- If MCP is available, confirm the module exists before writing the import.
- If a symbol is not found, the fix is almost always a missing or wrong import — not a redefinition.

## 5. No Axioms Unless Classical

Do not introduce `axiom` declarations. If a fact is missing, prove it, find it in Mathlib, or leave an explicit `sorry` with a documented plan.

The only acceptable axioms are those already in Lean's foundation:
- `Classical.choice`, `propext`, `Quot.sound`.

If you need classical reasoning (e.g., `by_cases`, `Decidable` on arbitrary props), use `open Classical` — that is normal and expected.

## 6. Do Not Suppress Warnings or Linter Output

Never insert `set_option` lines that hide problems:
- No `set_option linter.all false`.
- No `set_option linter.unusedVariables false` to mask real issues.
- No suppressing `sorry` warnings to make output look clean.

If a linter fires, it is flagging something real. Fix the cause, do not silence the symptom.

## 7. Small Proof Steps Over Hero Scripts

Preferred approach:
- Decompose into `have` blocks with clear intermediate goals. This is the single most effective proof structuring technique — it makes each step verifiable, names intermediate results, and prevents losing track of the proof state.
- Use short local proof blocks.
- Avoid large all-in-one proofs that are hard to debug.

If proof state becomes unclear, report current goals and propose the next single step.

## 8. Check Definitions Carefully

Before committing any new definition or structure:
- Verify that the type signature says what you intend. Read it back as a mathematical statement.
- Check that typeclass instances are correctly constructed — all required fields are provided and parent structures are properly extended.
- Ensure `instance` declarations do not duplicate or conflict with existing instances (this causes diamond problems where two paths to the same class produce non-definitionally-equal terms).
- After writing a definition, use it in at least one example or theorem to confirm it behaves as expected.

## 9. Use What You Create

Every helper lemma, definition, or intermediate construction you introduce must be used downstream in the proof or file. If you created a lemma and never applied it, something went wrong — either the proof strategy changed and the lemma is dead code, or you forgot to connect it.

- Before finishing, audit: is every `have`, `let`, `lemma`, and `def` you introduced actually referenced?
- Remove unused declarations. They signal a confused proof strategy and clutter the file.

## 10. `sorry` Discipline

A `sorry` is a promise, not a solution. Every `sorry` must be:
- Accompanied by a comment explaining what remains and the intended proof strategy.
- Counted and reported in your output.

Acceptable uses of `sorry`:
- Decomposing a problem top-down: sketch the structure with `sorry` placeholders, then fill them in one at a time.
- Temporarily isolating a subgoal you are actively working on.

Unacceptable uses:
- Leaving `sorry` without explanation.
- Using `sorry` to hide the fact that you do not know how to proceed.
- Claiming a proof is complete when `sorry` remains.

A file that compiles with `sorry` is scaffolding, not a result.

## 11. Definition Design Rules

For new definitions:
- Put assumptions in the right place (arguments vs typeclass constraints).
- Prefer structures already used in Mathlib.
- Keep names aligned with Lean/Mathlib conventions.
- Include a short doc comment only when not obvious.

## 12. Goal-Driven Verification Loop

Turn requests into verifiable loops:
1. Formalize target statement.
2. Check elaboration and missing imports.
3. Prove minimal working version.
4. Refactor for readability only if proof still checks.
5. Report what is done, what remains, and current blockers.

For bugfixes:
- First reproduce the failing theorem/error.
- Then apply smallest change that resolves it.

## 13. Surgical Edits

When modifying existing files:
- Touch only proof lines required for the request.
- Do not reformat unrelated sections.
- Keep local style consistent with the file.
- Remove only artifacts introduced by your own change.

## 14. Output Expectations

When returning a result, include:
- Final theorem/definition code.
- Required imports.
- Any assumptions you made.
- Remaining `sorry` count (if any), each with its intended resolution.