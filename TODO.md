# Rocqsheet TODO

All previously-listed items have a Coq-side contribution in the
tree; the residuals below are the parts that require work outside
this repository or substantial dedicated efforts that warrant their
own commits.

1. **`rocq-crane-imgui` actual repo split.** `rocq-crane-imgui/`
   has the migrated `ImGuiE.v` and `imgui_helpers.h`, but the
   directory is still inside this repository.  The split into a
   stand-alone GitHub repository, opam pin, and submodule
   conversion remains.

2. **`formula::eval_iter` formal correspondence.** `EvalIterSpec.v`
   exposes the `spec_value` alias the C++ runtime is expected to
   match.  A full simulation argument requires modelling
   `formula::eval_iter`'s small-step semantics in Coq or replacing
   the C++ implementation with one whose Coq model is auditable.
