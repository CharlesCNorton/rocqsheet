// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Move-aware C++ implementations of the workbook mutators that take
// loop_state by value (do_undo / do_redo / do_clear / do_insert_row
// / do_delete_row / do_swap_with_next_row).  Each consumes its
// argument and reconstructs the new loop_state via std::move on
// every nested field, so back-to-back operations under headless
// batch driving do not deep-clone the persistent unique_ptr<List<...>>
// chains carried on ls_other_sheets / ls_charts / ls_merges /
// ls_sheet_names / ls_edit_buf / ls_parse_errs / ls_undo / ls_redo /
// ls_formats.
//
// The Coq Definitions in theories/Edit.v stay as the executable
// spec; Crane Extract Inlined Constant directives redirect call
// sites here via lambda wrappers so the function value can still be
// passed to [cond_apply] (which is a template that accepts any
// callable).

#ifndef INCLUDED_DO_OP_HELPERS
#define INCLUDED_DO_OP_HELPERS

#include <cstdint>
#include <string>
#include <utility>
#include <variant>

namespace do_op_helpers {

// Maximum undo-stack depth.  Mirrors theories/State.v's
// [undo_max_depth].  Every push trims the head of ls_undo to this
// length so long-running sessions do not accumulate unbounded sheet
// snapshots on the heap.
constexpr unsigned int kUndoMaxDepth = 100;

// Trim a List<T> in place to at most [max_depth] entries by walking
// forward and severing the tail.
template <typename ListT>
inline ListT trim_undo(ListT xs, unsigned int max_depth = kUndoMaxDepth) {
  using Cons = typename ListT::Cons;
  if (max_depth == 0) return ListT::nil();
  ListT* cursor = &xs;
  unsigned int i = 0;
  while (cursor && std::holds_alternative<Cons>(cursor->v_mut())) {
    auto& c = std::get<Cons>(cursor->v_mut());
    if (i + 1 == max_depth) {
      c.d_a1 = std::make_unique<ListT>(ListT::nil());
      break;
    }
    cursor = c.d_a1.get();
    ++i;
  }
  return xs;
}

// Push the current ls_sheet onto ls_undo with [desc] as the action
// description, install [new_sheet] as the active sheet, and clear
// ls_redo.  Other workbook fields are moved through unchanged.
template <typename LoopState, typename Sheet, typename ListUndo>
inline LoopState commit_new_sheet(LoopState ls, Sheet new_sheet,
                                  std::string desc) {
  Sheet old_sheet = std::move(ls.ls_sheet);
  return LoopState{
    std::move(new_sheet),
    std::move(ls.ls_selected),
    std::move(ls.ls_fbar_text),
    std::move(ls.ls_edit_buf),
    std::move(ls.ls_parse_errs),
    trim_undo(
      ListUndo::cons(std::make_pair(std::move(old_sheet), std::move(desc)),
                     std::move(ls.ls_undo))),
    ListUndo::nil(),
    std::move(ls.ls_formats),
    std::move(ls.ls_other_sheets),
    ls.ls_active,
    std::move(ls.ls_charts),
    std::move(ls.ls_merges),
    std::move(ls.ls_sheet_names)};
}

// do_undo: pop ls_undo's head pair onto (ls_sheet, ...), push the
// previous (ls_sheet, popped_desc) onto ls_redo so redo carries the
// same description forward.
template <typename LoopState, typename Sheet, typename ListUndo>
inline LoopState do_undo(LoopState ls) {
  using Cons = typename ListUndo::Cons;
  using Nil  = typename ListUndo::Nil;
  if (std::holds_alternative<Nil>(ls.ls_undo.v())) {
    return ls;
  }
  auto& cons = std::get<Cons>(ls.ls_undo.v_mut());
  Sheet prev = std::move(cons.d_a0.first);
  std::string desc = std::move(cons.d_a0.second);
  ListUndo rest = cons.d_a1 ? std::move(*cons.d_a1) : ListUndo::nil();
  Sheet old_sheet = std::move(ls.ls_sheet);
  return LoopState{
    std::move(prev),
    std::move(ls.ls_selected),
    std::move(ls.ls_fbar_text),
    std::move(ls.ls_edit_buf),
    std::move(ls.ls_parse_errs),
    std::move(rest),
    ListUndo::cons(std::make_pair(std::move(old_sheet), std::move(desc)),
                   std::move(ls.ls_redo)),
    std::move(ls.ls_formats),
    std::move(ls.ls_other_sheets),
    ls.ls_active,
    std::move(ls.ls_charts),
    std::move(ls.ls_merges),
    std::move(ls.ls_sheet_names)};
  // Note: do_undo pushes onto ls_redo (not ls_undo), so we do not
  // trim here -- ls_redo is bounded by however many undos came before.
}

// do_redo: pop ls_redo's head pair onto (ls_sheet, ...), push the
// previous (ls_sheet, popped_desc) onto ls_undo.
template <typename LoopState, typename Sheet, typename ListUndo>
inline LoopState do_redo(LoopState ls) {
  using Cons = typename ListUndo::Cons;
  using Nil  = typename ListUndo::Nil;
  if (std::holds_alternative<Nil>(ls.ls_redo.v())) {
    return ls;
  }
  auto& cons = std::get<Cons>(ls.ls_redo.v_mut());
  Sheet next = std::move(cons.d_a0.first);
  std::string desc = std::move(cons.d_a0.second);
  ListUndo rest = cons.d_a1 ? std::move(*cons.d_a1) : ListUndo::nil();
  Sheet old_sheet = std::move(ls.ls_sheet);
  return LoopState{
    std::move(next),
    std::move(ls.ls_selected),
    std::move(ls.ls_fbar_text),
    std::move(ls.ls_edit_buf),
    std::move(ls.ls_parse_errs),
    trim_undo(
      ListUndo::cons(std::make_pair(std::move(old_sheet), std::move(desc)),
                     std::move(ls.ls_undo))),
    std::move(rest),
    std::move(ls.ls_formats),
    std::move(ls.ls_other_sheets),
    ls.ls_active,
    std::move(ls.ls_charts),
    std::move(ls.ls_merges),
    std::move(ls.ls_sheet_names)};
}

// do_clear: replace ls_sheet with [empty_sheet], reset ls_selected /
// ls_fbar_text / ls_edit_buf / ls_parse_errs, push (old ls_sheet,
// "clear sheet") onto undo, clear redo.
template <typename LoopState, typename Sheet, typename ListUndo,
          typename ListEdit, typename ListRefs>
inline LoopState do_clear(LoopState ls, Sheet empty_sheet) {
  Sheet old_sheet = std::move(ls.ls_sheet);
  return LoopState{
    std::move(empty_sheet),
    std::nullopt,
    std::string{},
    ListEdit::nil(),
    ListRefs::nil(),
    trim_undo(
      ListUndo::cons(std::make_pair(std::move(old_sheet),
                                    std::string("clear sheet")),
                     std::move(ls.ls_undo))),
    ListUndo::nil(),
    std::move(ls.ls_formats),
    std::move(ls.ls_other_sheets),
    ls.ls_active,
    std::move(ls.ls_charts),
    std::move(ls.ls_merges),
    std::move(ls.ls_sheet_names)};
}

// do_merge_right shape: install [new_merges] in place of ls.ls_merges
// and move every other field through.
template <typename LoopState, typename MergeList>
inline LoopState set_merges(LoopState ls, MergeList new_merges) {
  ls.ls_merges = std::move(new_merges);
  return ls;
}

// commit_via_selection: when [r] is selected, compute a new sheet via
// [transform] and commit it with [desc]; otherwise leave ls untouched.
template <typename LoopState, typename Sheet, typename ListUndo,
          typename Transform>
inline LoopState commit_via_selection(LoopState ls, std::string desc,
                                      Transform transform) {
  if (!ls.ls_selected.has_value()) {
    return ls;
  }
  auto r = *ls.ls_selected;
  Sheet new_sheet = transform(ls.ls_sheet, r);
  return commit_new_sheet<LoopState, Sheet, ListUndo>(
    std::move(ls), std::move(new_sheet), std::move(desc));
}

}  // namespace do_op_helpers

#endif  // INCLUDED_DO_OP_HELPERS
