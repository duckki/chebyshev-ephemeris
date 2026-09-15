# Ephemeris development workflow

- This is a standalone snapshot repository. Keep validation local; do not add CI
  or maintenance automation.

- Name modules by their contents, such as `Message` or
  `PositionReconstruction`; avoid vague names such as `Paper` or `Basic`.
- Keep `Ephemeris/` free of files, with the public `Ephemeris.lean` entry point
  outside that directory. Use direct imports and explicit Lake test targets;
  do not add per-directory import aggregators.
- `Ephemeris/Definitions/` contains source translations, explicit paper
  interpretations, and the authoritative decoded-input contract. Give each
  declaration a source location and representation rationale. Heavy review
  compares source claims with the paper and project choices with
  `docs/paper-and-spec.md`. `Definitions/Message` owns the selected input record,
  errors, bounded tick arithmetic, and executable guards; label these project
  policies separately from the published field allocation and external machine-number
  interpretations in earlier sections of the same module.
  `Definitions/PositionReconstruction` also contains the non-executable
  ideal real interpretation of that Message, in the module namespace. Keep `XYZ.map` with `XYZ`
  in `Definitions/Coordinates` as an explicitly labeled representation helper.
  Put other implementation adaptations in Implementation.
- Put original code and executable representation helpers in `Ephemeris/Implementation/`.
  Put correctness statements, statement-only relations, and their mathematical
  interpretation helpers in `Ephemeris/Implementation/Correctness/`, with one main
  contract module per implementation and separate shared relation modules.
  Review the code and contracts. Do not put actual theorems in Implementation
  except unavoidable termination helpers. Definitions must not import Implementation;
  neither layer may import proofs, tests, or oracle tooling. Maintain
  `docs/paper-and-spec.md` for source translations and project requirements.
- The executable Lean implementation is `Implementation/PositionReconstruction`.
  Use concrete native `Float` operations; keep the independent concrete `Float.Model`
  execution in `Implementation/Correctness/Float`. Do not add generic numeric
  kernels, backend classes, or a Rational implementation. Duplication between the
  native implementation and software model is intentional for readability.
  Runtime code must not import Correctness, proofs, tests, or oracle tooling,
  even transitively. Common decoded-input guards live in `Definitions/Message`.
  Native/Float proof modules and executable tests live at the roots of `Proofs/`
  and `Tests/`; `Proofs/Real/` proves the ideal source interpretation. Keep theorem
  leaf names stable and update qualified references, imports, and source links
  when reorganizing modules.
- Consolidate related declarations into reviewable modules: source field allocation
  and bounded-number interpretations together with the input contract in
  `Definitions/Message`; real equations,
  source loops and the ideal real Message interpretation in
  `Definitions/PositionReconstruction`. Put the independent polynomial semantics
  used as a correctness target in `Implementation/Correctness/Real`. Keep source domains and
  literal/interpreted formulas in clearly attributed sections. Keep shared
  `ReceiverError` in `Definitions/Message`
  and `XYZ.map` with `XYZ` in `Definitions/Coordinates`.
  The executable receiver lives in `Implementation/PositionReconstruction`.
  In Correctness, keep model execution and native Float contracts together in `Float`,
  and shared accuracy relations in `PositionAccuracy`. Keep `Real` for reviewable
  source-consistency claims and their independent polynomial comparison semantics,
  plus exact query interpretation and checked ideal evaluation. Do not add compatibility
  import aggregators. Match declaration namespaces to module file paths and avoid
  unnecessary nested namespaces. Shared types remain under `Ephemeris`, with
  methods under their type namespace; executable `main` stays at the root.
  In Correctness/Float, use `model`-prefixed execution names beside contracts.
  In Correctness/PositionAccuracy, use `RealWithin` and `Binary64Within`;
  do not reopen source namespaces for project correctness relations.
  Avoid redundant scalar reconstruction wrappers; the Message real model combines
  normalized time and the source position loop directly. Preserve the independent
  recurrence, loop, and polynomial views that the source-consistency proof compares.
- Keep Correctness limited to active contracts and the predicates/interpretations
  needed to understand them. `Message` retains `CoefficientFits`, `ValidMessage`,
  and `InWindow`. Put validation lemmas, intermediate natural tick helpers,
  and arithmetic-bridge lemmas in `Proofs/Message`. State intermediate lemma
  propositions directly in Proofs, without separate Correctness wrappers;
  this also applies to error composition and validation lemmas. Document planned
  upstream quantization in `docs/paper-and-spec.md`; do not add placeholder
  correctness definitions for unimplemented future functionality.
- Each reconstruction module exposes its own checked `evaluate` beside unchecked
  `reconstruct`. Share `ReceiverError` independently of numeric representation.
  The ideal Real, native Float, and software Float model evaluations share
  `Message.validateQuery` under the authoritative decoded-input contract. Reuse common checks
  when representations permit, and document any changed errors or precedence.
  Do not introduce a separate checked-receiver module. These validation policies
  are project requirements, not paper claims.
- Final Rust and Python float implementations must use binary64 and explicitly
  bounded integers only: no BigInt/BigRational, Fraction, Decimal, rational input
  normalization, or runtime rational error certificates. Python int values and
  intermediate results must satisfy the same width limits as Rust; do not rely
  on arbitrary-precision behavior. Keep unbounded arithmetic in Lean mathematical
  models, proofs, and model-oracle execution. Python differential tests use Lean Float.Model as their oracle;
  do not add a separate Fraction evaluator or sampled rational-error certificate.
- Refine Lean toward the bounded machine contract before porting native code.
  The authoritative decoded input is specified in `docs/paper-and-spec.md#decoded-input-contract`:
  degree 10, signed fixed-point coefficient integers at scale 2^-5 meters,
  Table 6 metadata, and the selected field ranges. There is exactly one primary
  `Message` type. This numerical component does not implement satellite serialization.
  Real and float working values are interpretations, not additional message formats. Compare float results to the real interpretation
  of this same integer message; do not treat arbitrary float inputs as the primary
  domain or add runtime rational coefficient conversions.
  The required path is the ideal real algorithm to a straightforward binary64
  implementation with a proved error bound. Keep purpose-specific optimizations
  separate from the primary specification and native API.
  Model integer overflow, normalization rounding, storage/loop bounds, finite
  inputs/results, and supported-domain success explicitly. Keep ghost radii and
  exact source embeddings in Correctness/Proofs/test tooling, outside Float
  runtime dependencies. Use native `Float` in `Implementation/PositionReconstruction`; keep explicit
  `Float.Model` execution in correctness semantics and oracle/test tooling. The
  runtime evaluator must not call the software model. Its independent oracle must
  execute model operations, not run the native evaluator and convert its output.
  Native and model execution have separate concrete normalization and loop
  definitions. They share the decoded Message and its validation policy.
  Prove their correspondence operation by operation.
  Prefer logically modeled native conversions; keep any necessary bounded conversion
  adaptation explicit with its correspondence contract. The model's internal
  big-number operations are not instructions to copy into Rust/Python.
  State and prove the new accuracy/refinement relation before calling a bounded
  replacement verified. Label unproved contracts separately from audited proofs.
- Preserve source notation, coefficient conventions, and algorithm structure
  where practical. Record ambiguities and corrections explicitly; keep literal
  source fragments separately from an interpreted algorithm when they differ.
- Interpret every adopted external source in its own mathematical or machine
  domain before adapting it. State numeric domains, units, indexing, exceptional
  values, and any inferred interpretation beside the relevant definitions.
  Refine explicitly from real semantics to finite precision with bounded error.
  Source algorithm definitions use concrete real arithmetic. Bounded fixed-point
  coefficients and ticks embed exactly into the real specification. Approximating
  arbitrary upstream reals or rounding arithmetic needs a separate error relation.
  Rational arithmetic used to interpret binary64 values belongs to the Lean
  mathematical model and proofs, not a separate reconstruction implementation.
  Keep conversion types explicit, including interpretations of library sources.
- Keep optimized or purpose-specific adaptations as separate definitions. State
  their relationship to the source algorithm and prove equivalence on the stated
  domain before claiming a verified replacement. For lossy transformations,
  specify the intended error relation explicitly.
- Keep correctness statements as definitions of propositions until a proof slice
  is authorized. Put completed proofs in `Ephemeris/Proofs/`; do not introduce
  admitted theorems or axioms to stand in for unfinished correctness work. Manual
  review of proof scripts is not required; Lean checks them. The specification,
  correctness statements, assumptions, and proof dependencies remain review inputs.
- Keep Lean oracle/protocol/benchmark construction in `Ephemeris/FuzzOracle/`
  for light review, and executable regression checks/audits in `Ephemeris/Tests/`.
- Keep the Python numerical implementation in
  `python/ephemeris/position_reconstruction.py`, with `Message`, tick arithmetic,
  and validation in `python/ephemeris/message.py`.
  The Python evaluator accepts the same bounded integer Message and tick as Lean.
  Put fuzz drivers,
  oracle servers, shared protocol/process/case helpers, and benchmarks under
  `python/fuzz/{drivers,oracles,shared,benchmarks}/`, with regression tests under
  `python/tests/`. Keep `python/fuzz/` alongside `ephemeris/` and `tests/`.
  The numerical package must not import testing infrastructure. Keep the oracle
  server independent of fuzz drivers and share protocol helpers explicitly.
- Run relevant checks and present a reviewable slice before committing. Commit
  only when the user requests it. After a commit, stop for review before the next
  slice unless the user has explicitly authorized continuing.

- Keep visitor/reviewer documentation in six guides directly under `docs/`:
  `paper-and-spec.md`, `lean-implementation.md`, `python-implementation.md`,
  `rust-implementation.md`, `fuzzing.md`, and `development.md`. Keep the root README
  a concise public introduction; put detailed setup, formatting, linting, and test
  commands in `development.md`. Put supporting research and estimates under `docs/references/`.
  Documentation and comments describe the release as a standalone snapshot;
  omit project chronology, retired designs, and references to prior commits.
  Preserve external source citations and pinned dependency references. Keep the source map and authoritative decoded input in
  `paper-and-spec.md`; keep proof status in `lean-implementation.md`.
- Rust's JSON process adapter belongs in `rust/src/fuzz.rs`, separate from the
  numerical kernel. Its module name and documentation must identify fuzz tooling.
