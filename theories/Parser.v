(* Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License. *)
(* Recursive-descent parser for cell formulas.  Operates on
   PrimString.string in pure Rocq, with char predicates lifted
   to PrimInt63 comparisons. *)

From Corelib Require Import PrimString PrimInt63 Uint63Axioms.
From Stdlib Require Import List Bool BinInt ZArith.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63 Sint63.
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Rocqsheet Require Import Rocqsheet.
Import ListNotations.
Import Rocqsheet.

(* int63 and Z both extract to int64_t under our mapping, so the
   axiomatic conversions are identity casts. *)
Crane Extract Inlined Constant Uint63Axioms.to_Z => "%a0".
Crane Extract Inlined Constant Uint63Axioms.of_Z => "%a0".

Open Scope int63_scope.
Local Open Scope pstring_scope.

(* PrimString.char63 maps to char in C++ extraction; in Rocq we
   treat it as an int63 and compare against the ASCII codepoints
   we recognise. *)
Axiom char_to_int : PrimString.char63 -> int.
Crane Extract Inlined Constant char_to_int =>
  "static_cast<int64_t>(static_cast<unsigned char>(%a0))".

Definition is_digit (c : PrimString.char63) : bool :=
  let n := char_to_int c in
  PrimInt63.leb 48 n && PrimInt63.leb n 57.

Definition is_upper (c : PrimString.char63) : bool :=
  let n := char_to_int c in
  PrimInt63.leb 65 n && PrimInt63.leb n 90.

Definition is_lower (c : PrimString.char63) : bool :=
  let n := char_to_int c in
  PrimInt63.leb 97 n && PrimInt63.leb n 122.

Definition is_alpha (c : PrimString.char63) : bool :=
  is_upper c || is_lower c.

Definition is_space (c : PrimString.char63) : bool :=
  let n := char_to_int c in
  orb (orb (PrimInt63.eqb n 32) (PrimInt63.eqb n 9))
      (orb (PrimInt63.eqb n 10) (PrimInt63.eqb n 13)).

Definition to_upper_int (n : int) : int :=
  if PrimInt63.leb 97 n && PrimInt63.leb n 122
  then PrimInt63.sub n 32 else n.

Definition digit_value (c : PrimString.char63) : Z :=
  let n := char_to_int c in
  Uint63.to_Z (PrimInt63.sub n 48).

Definition letter_index (c : PrimString.char63) : int :=
  PrimInt63.sub (to_upper_int (char_to_int c)) 65.

(* ----- Tokenization ----- *)

Inductive token : Type :=
  | TInt : Z -> token
  | TRef : CellRef -> token
  | TPlus
  | TMinus
  | TMul
  | TDiv
  | TEq
  | TLt
  | TGt
  | TLParen
  | TRParen
  | TComma
  | TIf
  | TMod
  | TPow
  | TNot
  | TAnd
  | TOr
  | TIfErr
  | TAvg
  | TCount.

(* INT64_MAX / 10 = 922337203685477580; one extra digit must not
   exceed (INT64_MAX mod 10) = 7. *)
Definition Z_int_max_div10 : Z := 922337203685477580%Z.
Definition Z_int_max_lastd : Z := 7%Z.

Definition acc_digit (acc : Z) (d : Z) : option Z :=
  if Z.ltb acc Z_int_max_div10 then Some (Z.add (Z.mul acc 10) d)
  else if Z.gtb acc Z_int_max_div10 then None
  else if Z.leb d Z_int_max_lastd then Some (Z.add (Z.mul acc 10) d)
  else None.

(* Read a run of digits starting at position [i] of [s].  Returns
   the accumulated value and the next position, or None on
   overflow.  Fuel is a hard bound on the number of digits read. *)
Fixpoint read_digits
    (fuel : nat) (s : PrimString.string) (len i : int) (acc : Z)
    (any : bool)
    : option (Z * int * bool) :=
  match fuel with
  | O => Some (acc, i, any)
  | S fuel' =>
    if PrimInt63.ltb i len then
      let c := PrimString.get s i in
      if is_digit c then
        match acc_digit acc (digit_value c) with
        | None => None
        | Some acc' =>
            read_digits fuel' s len (PrimInt63.add i 1) acc' true
        end
      else Some (acc, i, any)
    else Some (acc, i, any)
  end.

(* Skip whitespace.  Bounded by fuel; the live caller supplies
   [length s] which exceeds the worst-case run of spaces. *)
Fixpoint skip_ws (fuel : nat) (s : PrimString.string) (len i : int) : int :=
  match fuel with
  | O => i
  | S fuel' =>
    if PrimInt63.ltb i len then
      if is_space (PrimString.get s i)
      then skip_ws fuel' s len (PrimInt63.add i 1)
      else i
    else i
  end.

(* Try to read an integer literal starting at [i].  Returns the
   token plus the position past the last digit, or None if [i]
   does not point at a digit. *)
Definition read_int (fuel : nat) (s : PrimString.string) (len i : int)
    : option (Z * int) :=
  match read_digits fuel s len i 0%Z false with
  | Some (v, i', true) => Some (v, i')
  | _ => None
  end.

(* Try to read a cell reference: one or two letters (case-insensitive)
   followed by one or more digits.  Returns None if either piece is
   missing or out of range. *)
Definition read_ref (fuel : nat) (s : PrimString.string) (len i : int)
    : option (CellRef * int) :=
  if PrimInt63.ltb i len then
    let c1 := PrimString.get s i in
    if is_alpha c1 then
      let i1 := PrimInt63.add i 1 in
      let '(col, i2) :=
        if PrimInt63.ltb i1 len then
          let c2 := PrimString.get s i1 in
          if is_alpha c2 then
            (PrimInt63.add (PrimInt63.add 26 (PrimInt63.mul (letter_index c1) 26))
                           (letter_index c2),
             PrimInt63.add i1 1)
          else (letter_index c1, i1)
        else (letter_index c1, i1) in
      match read_int fuel s len i2 with
      | None => None
      | Some (row1, i3) =>
        if Z.leb row1 0 then None
        else
          let row := Z.sub row1 1 in
          if Z.geb row (Uint63.to_Z NUM_ROWS) then None
          else if PrimInt63.leb NUM_COLS col then None
          else
            let r := mkRef col (Uint63.of_Z row) in
            Some (r, i3)
      end
    else None
  else None.

(* Walk through the string emitting tokens.  Fuel is the number of
   characters; reaching it without consuming the whole string is a
   tokenizer bug. *)
Fixpoint tokenize_aux
    (fuel : nat) (s : PrimString.string) (len i : int)
    (acc : list token)
    : option (list token) :=
  match fuel with
  | O => None
  | S fuel' =>
    let i := skip_ws fuel s len i in
    if PrimInt63.leb len i then Some (rev acc)
    else
      let c := PrimString.get s i in
      let n := char_to_int c in
      if PrimInt63.eqb n 43 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TPlus :: acc)
      else if PrimInt63.eqb n 45 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TMinus :: acc)
      else if PrimInt63.eqb n 42 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TMul :: acc)
      else if PrimInt63.eqb n 47 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TDiv :: acc)
      else if PrimInt63.eqb n 61 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TEq :: acc)
      else if PrimInt63.eqb n 60 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TLt :: acc)
      else if PrimInt63.eqb n 62 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TGt :: acc)
      else if PrimInt63.eqb n 40 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TLParen :: acc)
      else if PrimInt63.eqb n 41 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TRParen :: acc)
      else if PrimInt63.eqb n 44 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TComma :: acc)
      else if PrimInt63.eqb n 37 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TMod :: acc)
      else if PrimInt63.eqb n 94 then
        tokenize_aux fuel' s len (PrimInt63.add i 1) (TPow :: acc)
      else if is_digit c then
        match read_int fuel s len i with
        | None => None
        | Some (v, i') => tokenize_aux fuel' s len i' (TInt v :: acc)
        end
      else if is_alpha c then
        let c0 := to_upper_int (char_to_int c) in
        let i1 := PrimInt63.add i 1 in
        let i2 := PrimInt63.add i 2 in
        let i3 := PrimInt63.add i 3 in
        let i4 := PrimInt63.add i 4 in
        let i5 := PrimInt63.add i 5 in
        let i6 := PrimInt63.add i 6 in
        let i7 := PrimInt63.add i 7 in
        let i8 := PrimInt63.add i 8 in
        let chr j :=
          if PrimInt63.ltb j len then to_upper_int (char_to_int (PrimString.get s j))
          else 0 in
        let lparen j :=
          PrimInt63.ltb j len &&
          PrimInt63.eqb (char_to_int (PrimString.get s j)) 40 in
        let c1u := chr i1 in
        let c2u := chr i2 in
        let c3u := chr i3 in
        let c4u := chr i4 in
        let c5u := chr i5 in
        let c6u := chr i6 in
        let seven_letter_kw_lp := lparen i7 in
        let five_letter_kw_lp := lparen i5 in
        let three_letter_kw_lp := lparen i3 in
        if PrimInt63.eqb c0 73 && PrimInt63.eqb c1u 70 &&
           PrimInt63.eqb c2u 69 && PrimInt63.eqb c3u 82 &&
           PrimInt63.eqb c4u 82 && PrimInt63.eqb c5u 79 &&
           PrimInt63.eqb c6u 82 && seven_letter_kw_lp
        then
          (* "IFERROR(" *)
          tokenize_aux fuel' s len i8 (TIfErr :: acc)
        else if PrimInt63.eqb c0 67 && PrimInt63.eqb c1u 79 &&
                PrimInt63.eqb c2u 85 && PrimInt63.eqb c3u 78 &&
                PrimInt63.eqb c4u 84 && five_letter_kw_lp
        then
          (* "COUNT(" *)
          tokenize_aux fuel' s len i6 (TCount :: acc)
        else if PrimInt63.eqb c0 78 && PrimInt63.eqb c1u 79 &&
                PrimInt63.eqb c2u 84 && three_letter_kw_lp
        then
          tokenize_aux fuel' s len i4 (TNot :: acc)
        else if PrimInt63.eqb c0 65 && PrimInt63.eqb c1u 78 &&
                PrimInt63.eqb c2u 68 && three_letter_kw_lp
        then
          tokenize_aux fuel' s len i4 (TAnd :: acc)
        else if PrimInt63.eqb c0 65 && PrimInt63.eqb c1u 86 &&
                PrimInt63.eqb c2u 71 && three_letter_kw_lp
        then
          (* "AVG(" *)
          tokenize_aux fuel' s len i4 (TAvg :: acc)
        else
          let two_letter_kw_lp := lparen i2 in
          if PrimInt63.eqb c0 73 && PrimInt63.eqb c1u 70 && two_letter_kw_lp
          then
            tokenize_aux fuel' s len i3 (TIf :: acc)
          else if PrimInt63.eqb c0 79 && PrimInt63.eqb c1u 82 && two_letter_kw_lp
          then
            tokenize_aux fuel' s len i3 (TOr :: acc)
          else
            match read_ref fuel s len i with
            | None => None
            | Some (r, i') => tokenize_aux fuel' s len i' (TRef r :: acc)
            end
      else None
  end.

Definition tokenize (s : PrimString.string) : option (list token) :=
  let len := PrimString.length s in
  let fuel := S (nat_of_int len) in
  tokenize_aux fuel s len 0 [].

(* ----- Parsing ----- *)

(* Recursive descent.  Each non-terminal returns the parsed Expr
   plus the remaining tokens, or None on syntax error. *)

Fixpoint parse_top (fuel : nat) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => None
  | S fuel' =>
    match parse_expr fuel' toks with
    | None => None
    | Some (lhs, rest) =>
      match rest with
      | TEq :: rest' =>
        match parse_expr fuel' rest' with
        | Some (rhs, rest'') => Some (EEq lhs rhs, rest'')
        | None => None
        end
      | TLt :: rest' =>
        match parse_expr fuel' rest' with
        | Some (rhs, rest'') => Some (ELt lhs rhs, rest'')
        | None => None
        end
      | TGt :: rest' =>
        match parse_expr fuel' rest' with
        | Some (rhs, rest'') => Some (EGt lhs rhs, rest'')
        | None => None
        end
      | _ => Some (lhs, rest)
      end
    end
  end

with parse_expr (fuel : nat) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => None
  | S fuel' =>
    match parse_term fuel' toks with
    | None => None
    | Some (lhs, rest) => parse_expr_tail fuel' lhs rest
    end
  end

with parse_expr_tail (fuel : nat) (lhs : Expr) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => Some (lhs, toks)
  | S fuel' =>
    match toks with
    | TPlus :: rest =>
      match parse_term fuel' rest with
      | Some (rhs, rest') => parse_expr_tail fuel' (EAdd lhs rhs) rest'
      | None => None
      end
    | TMinus :: rest =>
      match parse_term fuel' rest with
      | Some (rhs, rest') => parse_expr_tail fuel' (ESub lhs rhs) rest'
      | None => None
      end
    | _ => Some (lhs, toks)
    end
  end

with parse_term (fuel : nat) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => None
  | S fuel' =>
    match parse_factor fuel' toks with
    | None => None
    | Some (lhs, rest) => parse_term_tail fuel' lhs rest
    end
  end

with parse_term_tail (fuel : nat) (lhs : Expr) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => Some (lhs, toks)
  | S fuel' =>
    match toks with
    | TMul :: rest =>
      match parse_factor fuel' rest with
      | Some (rhs, rest') => parse_term_tail fuel' (EMul lhs rhs) rest'
      | None => None
      end
    | TDiv :: rest =>
      match parse_factor fuel' rest with
      | Some (rhs, rest') => parse_term_tail fuel' (EDiv lhs rhs) rest'
      | None => None
      end
    | TMod :: rest =>
      match parse_factor fuel' rest with
      | Some (rhs, rest') => parse_term_tail fuel' (EMod lhs rhs) rest'
      | None => None
      end
    | TPow :: rest =>
      match parse_factor fuel' rest with
      | Some (rhs, rest') => parse_term_tail fuel' (EPow lhs rhs) rest'
      | None => None
      end
    | _ => Some (lhs, toks)
    end
  end

with parse_factor (fuel : nat) (toks : list token)
    : option (Expr * list token) :=
  match fuel with
  | O => None
  | S fuel' =>
    match toks with
    | TMinus :: rest =>
      match parse_factor fuel' rest with
      | Some (e, rest') => Some (ESub (EInt 0%Z) e, rest')
      | None => None
      end
    | TLParen :: rest =>
      match parse_top fuel' rest with
      | Some (e, TRParen :: rest') => Some (e, rest')
      | _ => None
      end
    | TInt n :: rest => Some (EInt n, rest)
    | TRef r :: rest => Some (ERef r, rest)
    | TIf :: rest =>
      match parse_top fuel' rest with
      | Some (cnd, TComma :: rest1) =>
        match parse_top fuel' rest1 with
        | Some (th, TComma :: rest2) =>
          match parse_top fuel' rest2 with
          | Some (el, TRParen :: rest3) => Some (EIf cnd th el, rest3)
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | TNot :: rest =>
      match parse_top fuel' rest with
      | Some (a, TRParen :: rest') => Some (ENot a, rest')
      | _ => None
      end
    | TAnd :: rest =>
      match parse_top fuel' rest with
      | Some (a, TComma :: rest1) =>
        match parse_top fuel' rest1 with
        | Some (b, TRParen :: rest2) => Some (EAnd a b, rest2)
        | _ => None
        end
      | _ => None
      end
    | TOr :: rest =>
      match parse_top fuel' rest with
      | Some (a, TComma :: rest1) =>
        match parse_top fuel' rest1 with
        | Some (b, TRParen :: rest2) => Some (EOr a b, rest2)
        | _ => None
        end
      | _ => None
      end
    | TIfErr :: rest =>
      match parse_top fuel' rest with
      | Some (a, TComma :: rest1) =>
        match parse_top fuel' rest1 with
        | Some (fb, TRParen :: rest2) => Some (EIfErr a fb, rest2)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

(* ----- Top-level entry points ----- *)

Definition parse_formula (s : PrimString.string) : option Expr :=
  match tokenize s with
  | None => None
  | Some toks =>
    (* parse_top -> parse_expr -> parse_term -> parse_factor consumes
       four levels per leaf, plus deeper nesting through TLParen,
       TMinus, and TIf.  The bound is linear in token count with a
       constant safety margin. *)
    let fuel := plus 100 (mult 8 (length toks)) in
    match parse_top fuel toks with
    | Some (e, []) => Some e
    | _ => None
    end
  end.

(* Standalone integer-literal parser used for non-formula cell
   input.  Accepts surrounding whitespace and an optional leading
   minus sign. *)
Definition parse_int_literal (s : PrimString.string) : option Z :=
  let len := PrimString.length s in
  let fuel := S (nat_of_int len) in
  let i := skip_ws fuel s len 0 in
  let '(neg, j) :=
    if PrimInt63.ltb i len &&
       PrimInt63.eqb (char_to_int (PrimString.get s i)) 45
    then (true, PrimInt63.add i 1) else (false, i) in
  match read_digits fuel s len j 0%Z false with
  | Some (v, k, true) =>
      let k' := skip_ws fuel s len k in
      if PrimInt63.leb len k' then
        Some (if neg then Z.opp v else v)
      else None
  | _ => None
  end.

