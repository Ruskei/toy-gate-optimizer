import std/times
import std/monotimes
import std/tables
import std/sets
import std/strutils
import std/sequtils

type
  NullaryGateKind = enum
    gk_none,
    gk_input_x,
    gk_input_y,
    gk_input_z,
    gk_const_0,
    gk_const_1,
  UnaryGateKind = enum
    gk_not,
  BinaryGateKind = enum
    gk_and,
    gk_nand,
    gk_or,
    gk_nor,
    gk_xor,
  WitnessType = enum
    gt_unary,
    gt_binary,
  Witness = object
    case gate_type: WitnessType
    of gt_unary:
      u_kind: UnaryGateKind
      u_root_signal: uint8
      u_child_1: uint8
      u_local_cost: int
    of gt_binary:
      b_kind: BinaryGateKind
      b_root_signal: uint8
      b_child_1: uint8
      b_child_2: uint8
      b_local_cost: int
  WitnessID = int
  WitnessData = object
    all_witnesses: seq[Witness]
    witnesses_by_child_1: array[256, seq[WitnessID]]
    witnesses_by_child_2: array[256, seq[WitnessID]]
  GateContext = object
    allowed_nullary_gates: seq[NullaryGateKind]
    allowed_unary_gates: seq[UnaryGateKind]
    allowed_binary_gates: seq[BinaryGateKind]
  BuiltSignalState = array[4, uint64] # 256 bits
  SearchResult = object
    min_gates: int
    used_witness_ids: seq[WitnessID]
  OptimizeResult = object
    min_gates: int
    used_witnesses: seq[Witness]
  OptimizeRun* = object
    min_gates*: int
    generation_ms*: int64
    total_ms*: int64
    optimize_result: OptimizeResult
  SearchState = object
    built_state: BuiltSignalState
    missing_children_counts: seq[uint8]
    enabled_witnesses: seq[WitnessID]
    used_witness_ids: seq[WitnessID]
    num_gates_used: int
  UndoEntry = object
    witness_id: WitnessID
    old_value: uint8

const
  unreached_cost = high(int)
  input_x_signal: uint8 = 0b11110000'u8
  input_y_signal: uint8 = 0b11001100'u8
  input_z_signal: uint8 = 0b10101010'u8

proc root_signal(witness: Witness): uint8 =
  case witness.gate_type
  of gt_unary: witness.u_root_signal
  of gt_binary: witness.b_root_signal

proc eval_nullary_gate(gate_kind: NullaryGateKind): uint8 =
  case gate_kind
  of gk_input_x: input_x_signal
  of gk_input_y: input_y_signal
  of gk_input_z: input_z_signal
  of gk_const_0: 0x00'u8
  of gk_const_1: 0xFF'u8
  of gk_none:
    raise newException(ValueError, "gk_none is not a realizable nullary gate")

proc eval_unary_gate(gate_kind: UnaryGateKind, child_signal: uint8): uint8 =
  case gate_kind
  of gk_not:
    not child_signal

proc eval_binary_gate(
  gate_kind: BinaryGateKind,
  left_signal, right_signal: uint8
): uint8 =
  case gate_kind
  of gk_and:
    left_signal and right_signal
  of gk_nand:
    not (left_signal and right_signal)
  of gk_or:
    left_signal or right_signal
  of gk_nor:
    not (left_signal or right_signal)
  of gk_xor:
    left_signal xor right_signal

proc initial_signals(context: GateContext): seq[uint8] =
  result = @[]
  for nullary_gate in context.allowed_nullary_gates:
    let signal = eval_nullary_gate(nullary_gate)
    var already_present = false
    for existing_signal in result:
      if existing_signal == signal:
        already_present = true
        break
    if not already_present:
      result.add signal

proc gates_needed(gate_context: GateContext, output: uint8): int =
  var best_cost: array[256, int]
  for i in 0 .. high(best_cost):
    best_cost[i] = unreached_cost

  var frontiers: seq[seq[uint8]] = @[]
  frontiers.add @[]

  for nullary_gate in gate_context.allowed_nullary_gates:
    let base_signal = eval_nullary_gate(nullary_gate)
    if best_cost[int(base_signal)] == unreached_cost:
      best_cost[int(base_signal)] = 0
      frontiers[0].add base_signal

  if best_cost[int(output)] != unreached_cost:
    return 0

  var total_cost = 1
  while true:
    frontiers.add @[]

    for unary_gate in gate_context.allowed_unary_gates:
      for child_signal in frontiers[total_cost - 1]:
        let result_signal = eval_unary_gate(unary_gate, child_signal)
        if best_cost[int(result_signal)] != unreached_cost:
          continue

        best_cost[int(result_signal)] = total_cost
        if result_signal == output:
          return total_cost
        frontiers[total_cost].add result_signal

    for left_cost in 0 ..< total_cost:
      let right_cost = (total_cost - 1) - left_cost

      if left_cost > right_cost:
        continue

      for left_signal in frontiers[left_cost]:
        for right_signal in frontiers[right_cost]:
          if left_cost == right_cost and left_signal > right_signal:
            continue

          for binary_gate in gate_context.allowed_binary_gates:
            let result_signal = eval_binary_gate(binary_gate, left_signal, right_signal)
            if best_cost[int(result_signal)] != unreached_cost:
              continue

            best_cost[int(result_signal)] = total_cost
            if result_signal == output:
              return total_cost
            frontiers[total_cost].add result_signal

    if frontiers[total_cost].len == 0:
      return unreached_cost

    inc total_cost

  result = total_cost

proc generate_witnesses(
  gate_context: GateContext,
  outs: seq[uint8],
  generation_ms: var int64,
): WitnessData =
  let start = get_mono_time()

  var upper_bound = 0
  for output in outs:
    let cost = gate_context.gates_needed(output)
    if cost == unreached_cost:
      generation_ms = in_milliseconds(get_mono_time() - start)
      return
    upper_bound += cost

  var best_cost: array[256, int]
  for i in 0 .. high(best_cost):
    best_cost[i] = unreached_cost

  var frontiers: seq[seq[uint8]] = @[]
  frontiers.add @[]

  template add_witness(new_witness: Witness) =
    let witness_id: WitnessID = result.all_witnesses.len
    result.all_witnesses.add new_witness
    case new_witness.gate_type
    of gt_unary:
      result.witnesses_by_child_1[int(new_witness.u_child_1)].add witness_id
    of gt_binary:
      result.witnesses_by_child_1[int(new_witness.b_child_1)].add witness_id
      result.witnesses_by_child_2[int(new_witness.b_child_2)].add witness_id

  for nullary_gate in gate_context.allowed_nullary_gates:
    let base_signal = eval_nullary_gate(nullary_gate)
    if best_cost[int(base_signal)] == unreached_cost:
      best_cost[int(base_signal)] = 0
      frontiers[0].add base_signal

  for total_cost in 1 .. upper_bound:
    frontiers.add @[]

    for unary_gate in gate_context.allowed_unary_gates:
      for child_1_signal in frontiers[total_cost - 1]:
        let root_signal = eval_unary_gate(unary_gate, child_1_signal)

        add_witness Witness(
          gate_type: gt_unary,
          u_kind: unary_gate,
          u_root_signal: root_signal,
          u_child_1: child_1_signal,
          u_local_cost: total_cost,
        )

        if best_cost[int(root_signal)] == unreached_cost:
          best_cost[int(root_signal)] = total_cost
          frontiers[total_cost].add root_signal

    for left_cost in 0 ..< total_cost:
      let right_cost = (total_cost - 1) - left_cost

      if left_cost > right_cost:
        continue

      for child_1_signal in frontiers[left_cost]:
        for child_2_signal in frontiers[right_cost]:
          if left_cost == right_cost and child_1_signal > child_2_signal:
            continue

          for binary_gate in gate_context.allowed_binary_gates:
            let root_signal = eval_binary_gate(binary_gate, child_1_signal, child_2_signal)

            add_witness Witness(
              gate_type: gt_binary,
              b_kind: binary_gate,
              b_root_signal: root_signal,
              b_child_1: child_1_signal,
              b_child_2: child_2_signal,
              b_local_cost: total_cost,
            )

            if best_cost[int(root_signal)] == unreached_cost:
              best_cost[int(root_signal)] = total_cost
              frontiers[total_cost].add root_signal

  generation_ms = in_milliseconds(get_mono_time() - start)

proc contains_signal(state: BuiltSignalState, signal: uint8): bool =
  let signal_index = int(signal)
  let word_index = signal_index shr 6
  let bit_index = signal_index and 63
  ((state[word_index] shr bit_index) and 1'u64) != 0

proc incl_signal(state: var BuiltSignalState, signal: uint8) =
  let signal_index = int(signal)
  let word_index = signal_index shr 6
  let bit_index = signal_index and 63
  state[word_index] = state[word_index] or (1'u64 shl bit_index)

proc excl_signal(state: var BuiltSignalState, signal: uint8) =
  let signal_index = int(signal)
  let word_index = signal_index shr 6
  let bit_index = signal_index and 63
  state[word_index] = state[word_index] and (not (1'u64 shl bit_index))

proc to_built_signal_state(signals: openArray[uint8]): BuiltSignalState =
  for signal in signals:
    result.incl_signal(signal)

proc outputs_satisfied(state: BuiltSignalState, outs: seq[uint8]): bool =
  for output in outs:
    if not state.contains_signal(output):
      return false
  true

proc missing_output_count(state: BuiltSignalState, outs: seq[uint8]): int =
  for output in outs:
    if not state.contains_signal(output):
      inc result

proc build_witnesses_by_root(witness_data: WitnessData): array[256, seq[WitnessID]] =
  for witness_id, witness in witness_data.all_witnesses:
    result[int(root_signal(witness))].add witness_id

proc compute_relevant_signals(
  outs: seq[uint8],
  witness_data: WitnessData
): array[256, bool] =
  let witnesses_by_root = build_witnesses_by_root(witness_data)

  var stack = outs
  while stack.len > 0:
    let signal = stack[^1]
    stack.set_len(stack.len - 1)

    if result[int(signal)]:
      continue
    result[int(signal)] = true

    for witness_id in witnesses_by_root[int(signal)]:
      let witness = witness_data.all_witnesses[witness_id]
      case witness.gate_type
      of gt_unary:
        if not result[int(witness.u_child_1)]:
          stack.add witness.u_child_1
      of gt_binary:
        if not result[int(witness.b_child_1)]:
          stack.add witness.b_child_1
        if not result[int(witness.b_child_2)]:
          stack.add witness.b_child_2

proc initialize_missing_counts_and_enabled(
  initial_state: BuiltSignalState,
  outs: seq[uint8],
  witness_data: WitnessData,
): tuple[
  relevant_signals: array[256, bool],
  missing_children_counts: seq[uint8],
  enabled_witnesses: seq[WitnessID],
] =
  result.relevant_signals = compute_relevant_signals(outs, witness_data)
  result.missing_children_counts = new_seq[uint8](witness_data.all_witnesses.len)

  for witness_id, witness in witness_data.all_witnesses:
    let root = root_signal(witness)
    if not result.relevant_signals[int(root)]:
      continue

    var missing_count = 0
    case witness.gate_type
    of gt_unary:
      if not initial_state.contains_signal(witness.u_child_1):
        inc missing_count
    of gt_binary:
      if not initial_state.contains_signal(witness.b_child_1):
        inc missing_count
      if witness.b_child_2 != witness.b_child_1:
        if not initial_state.contains_signal(witness.b_child_2):
          inc missing_count

    result.missing_children_counts[witness_id] = uint8(missing_count)

    if missing_count == 0 and not initial_state.contains_signal(root):
      result.enabled_witnesses.add witness_id

proc optimize_gates_needed(
  built_signals: seq[uint8],
  outs: seq[uint8],
  witness_data: WitnessData,
): OptimizeResult =
  let initial_state = to_built_signal_state(built_signals)
  if initial_state.outputs_satisfied(outs):
    result.min_gates = 0
    result.used_witnesses = @[]
    return

  let init = initialize_missing_counts_and_enabled(initial_state, outs, witness_data)

  var state = SearchState(
    built_state: initial_state,
    missing_children_counts: init.missing_children_counts,
    enabled_witnesses: init.enabled_witnesses,
    used_witness_ids: @[],
    num_gates_used: 0,
  )

  var undo_log: seq[UndoEntry] = @[]

  var memo: Table[BuiltSignalState, SearchResult]
  var best_found = unreached_cost

  # Returns the suffix result from the CURRENT state:
  # - min_gates is the number of ADDITIONAL gates needed from here
  # - used_witness_ids is the witness suffix from here
  proc solve(): SearchResult =
    var best_result = SearchResult(min_gates: unreached_cost, used_witness_ids: @[])

    let enabled_len = state.enabled_witnesses.len
    for idx in 0 ..< enabled_len:
      let witness_id = state.enabled_witnesses[idx]
      if state.missing_children_counts[witness_id] > 0:
        continue

      let witness = witness_data.all_witnesses[witness_id]
      let root = witness.root_signal
      if state.built_state.contains_signal(root):
        continue

      let undo_log_checkpoint = undo_log.len

      block recurse:
        inc state.num_gates_used
        state.used_witness_ids.add witness_id
        state.built_state.incl_signal(root)

        let lower_bound = missing_output_count(state.built_state, outs)
        if best_found != unreached_cost and state.num_gates_used + lower_bound >= best_found:
          break recurse

        # base case: this one added gate finished the solution
        if state.built_state.outputs_satisfied(outs):
          if state.num_gates_used < best_found:
            best_found = state.num_gates_used

          let candidate_result = SearchResult(
            min_gates: 1,
            used_witness_ids: @[witness_id],
          )
          if candidate_result.min_gates < best_result.min_gates:
            best_result = candidate_result
          break recurse

        # memoized suffix from the state AFTER adding this witness
        if state.built_state in memo:
          let memoized_result = memo[state.built_state]
          if memoized_result.min_gates != unreached_cost:
            let total_gates = state.num_gates_used + memoized_result.min_gates
            if total_gates < best_found:
              best_found = total_gates

            let candidate_result = SearchResult(
              min_gates: 1 + memoized_result.min_gates,
              used_witness_ids: @[witness_id] & memoized_result.used_witness_ids,
            )
            if candidate_result.min_gates < best_result.min_gates:
              best_result = candidate_result
          break recurse

        for affected_witness_id in witness_data.witnesses_by_child_1[int(root)]:
          let affected_missing_children_count = state.missing_children_counts[affected_witness_id]
          if affected_missing_children_count == 0:
            continue

          dec state.missing_children_counts[affected_witness_id]
          undo_log.add UndoEntry(
            witness_id: affected_witness_id,
            old_value: affected_missing_children_count,
          )

          if state.missing_children_counts[affected_witness_id] == 0:
            let affected_root = witness_data.all_witnesses[affected_witness_id].root_signal
            if init.relevant_signals[int(affected_root)] and not state.built_state.contains_signal(affected_root):
              state.enabled_witnesses.add affected_witness_id

        for affected_witness_id in witness_data.witnesses_by_child_2[int(root)]:
          let affected_missing_children_count = state.missing_children_counts[affected_witness_id]
          if affected_missing_children_count == 0:
            continue

          let affected_witness = witness_data.all_witnesses[affected_witness_id]
          if affected_witness.b_child_1 == root:
            continue

          dec state.missing_children_counts[affected_witness_id]
          undo_log.add UndoEntry(
            witness_id: affected_witness_id,
            old_value: affected_missing_children_count,
          )

          if state.missing_children_counts[affected_witness_id] == 0:
            let affected_root = witness_data.all_witnesses[affected_witness_id].root_signal
            if init.relevant_signals[int(affected_root)] and not state.built_state.contains_signal(affected_root):
              state.enabled_witnesses.add affected_witness_id

        let next_result = solve()
        if next_result.min_gates != unreached_cost:
          let total_gates = state.num_gates_used + next_result.min_gates
          if total_gates < best_found:
            best_found = total_gates

          let candidate_result = SearchResult(
            min_gates: 1 + next_result.min_gates,
            used_witness_ids: @[witness_id] & next_result.used_witness_ids,
          )
          if candidate_result.min_gates < best_result.min_gates:
            best_result = candidate_result

      dec state.num_gates_used
      state.used_witness_ids.set_len(state.used_witness_ids.len - 1)
      state.built_state.excl_signal(root)
      state.enabled_witnesses.set_len(enabled_len)

      while undo_log.len > undo_log_checkpoint:
        let undo_entry = undo_log.pop()
        state.missing_children_counts[undo_entry.witness_id] = undo_entry.old_value

    memo[state.built_state] = best_result

    result = best_result

  let root_result = solve()

  if root_result.min_gates == unreached_cost:
    result.min_gates = unreached_cost
    result.used_witnesses = @[]
    return

  result.min_gates = root_result.min_gates
  result.used_witnesses = new_seq[Witness](root_result.used_witness_ids.len)
  for i, witness_id in root_result.used_witness_ids:
    result.used_witnesses[i] = witness_data.all_witnesses[witness_id]

proc signal_label(truth_table: uint8): string =
  if truth_table == input_z_signal: "Z"
  elif truth_table == input_y_signal: "Y"
  elif truth_table == input_x_signal: "X"
  elif truth_table == 0'u8: "0"
  elif truth_table == 0xFF'u8: "1"
  else: "0b" & to_bin(int(truth_table), 8)

proc gate_name(gate_kind: UnaryGateKind): string =
  case gate_kind
  of gk_not: "NOT"

proc gate_name(gate_kind: BinaryGateKind): string =
  case gate_kind
  of gk_and: "AND"
  of gk_nand: "NAND"
  of gk_or: "OR"
  of gk_nor: "NOR"
  of gk_xor: "XOR"

proc format_signal_ref(
  signal: uint8,
  witness_index_by_root: Table[uint8, int],
): string =
  if signal in witness_index_by_root:
    "w" & $witness_index_by_root[signal]
  else:
    signal_label(signal)

proc format_witness_expr(
  signal: uint8,
  witness_by_root: Table[uint8, Witness],
  max_depth: int = 64,
  depth: int = 0,
): string =
  if depth >= max_depth:
    return "<depth>"

  if signal notin witness_by_root:
    return signal_label(signal)

  let witness = witness_by_root[signal]
  case witness.gate_type
  of gt_unary:
    gate_name(witness.u_kind) & "(" &
      format_witness_expr(witness.u_child_1, witness_by_root, max_depth, depth + 1) &
      ")"
  of gt_binary:
    gate_name(witness.b_kind) & "(" &
      format_witness_expr(witness.b_child_1, witness_by_root, max_depth, depth + 1) &
      ", " &
      format_witness_expr(witness.b_child_2, witness_by_root, max_depth, depth + 1) &
      ")"

proc format_witness_definition(
  witness: Witness,
  witness_index_by_root: Table[uint8, int],
): string =
  case witness.gate_type
  of gt_unary:
    gate_name(witness.u_kind) & "(" &
      format_signal_ref(witness.u_child_1, witness_index_by_root) &
      ")"
  of gt_binary:
    gate_name(witness.b_kind) & "(" &
      format_signal_ref(witness.b_child_1, witness_index_by_root) & ", " &
      format_signal_ref(witness.b_child_2, witness_index_by_root) &
      ")"

proc format_optimize_result(
  outs: seq[uint8],
  optimize_result: OptimizeResult,
) =
  if optimize_result.min_gates == unreached_cost:
    echo "No solution."
    return

  var witness_by_root: Table[uint8, Witness]
  var witness_index_by_root: Table[uint8, int]

  for i, witness in optimize_result.used_witnesses:
    let root = root_signal(witness)
    witness_by_root[root] = witness
    witness_index_by_root[root] = i

  echo "Solved."
  for output_signal in outs:
    let expr =
      if output_signal in witness_by_root:
        format_witness_expr(output_signal, witness_by_root)
      else:
        signal_label(output_signal)
    echo signal_label(output_signal), "  expr=", expr

  echo "Total gates needed=", optimize_result.min_gates
  echo "Unique gate nodes:"
  for i, witness in optimize_result.used_witnesses:
    let root = root_signal(witness)
    echo "  w", i, " [", signal_label(root), "] = ",
         format_witness_definition(witness, witness_index_by_root)

proc capture_optimize_run*(
  outs: seq[uint8],
  enable_not: bool = true,
  enable_and: bool = true,
  enable_nand: bool = true,
  enable_or: bool = true,
  enable_nor: bool = true,
  enable_xor: bool = true,
): OptimizeRun =
  let unique_outs = outs.deduplicate
  let start = get_mono_time()

  var allowed_unary_gates: seq[UnaryGateKind] = @[]
  if enable_not:
    allowed_unary_gates.add gk_not

  var allowed_binary_gates: seq[BinaryGateKind] = @[]
  if enable_nand:
    allowed_binary_gates.add gk_nand
  if enable_and:
    allowed_binary_gates.add gk_and
  if enable_xor:
    allowed_binary_gates.add gk_xor
  if enable_or:
    allowed_binary_gates.add gk_or
  if enable_nor:
    allowed_binary_gates.add gk_nor

  let context = GateContext(
    allowed_nullary_gates: @[
      gk_input_x,
      gk_input_y,
      gk_input_z,
      gk_const_0,
      gk_const_1,
    ],
    allowed_unary_gates: allowed_unary_gates,
    allowed_binary_gates: allowed_binary_gates,
  )

  var generation_ms: int64 = 0
  let witness_data = generate_witnesses(context, unique_outs, generation_ms)
  let initial_signals = context.initial_signals
  let optimize_result = optimize_gates_needed(initial_signals, unique_outs, witness_data)

  let finish = get_mono_time()
  result.min_gates = optimize_result.min_gates
  result.generation_ms = generation_ms
  result.total_ms = in_milliseconds(finish - start)
  result.optimize_result = optimize_result

proc print_optimize_run*(outs: seq[uint8], run: OptimizeRun) =
  let unique_outs = outs.deduplicate
  echo "generating witnesses took ", run.generation_ms, "ms"
  echo run.min_gates
  format_optimize_result(unique_outs, run.optimize_result)
  echo "fully optimizing logic took ", run.total_ms, "ms"

proc fully_optimize_logic*(
  outs: seq[uint8],
  enable_not: bool = true,
  enable_and: bool = true,
  enable_nand: bool = true,
  enable_or: bool = true,
  enable_nor: bool = true,
  enable_xor: bool = true,
) =
  let run = capture_optimize_run(
    outs,
    enable_not = enable_not,
    enable_and = enable_and,
    enable_nand = enable_nand,
    enable_or = enable_or,
    enable_nor = enable_nor,
    enable_xor = enable_xor,
  )
  print_optimize_run(outs, run)
