import std/times
import std/monotimes
import std/algorithm
import std/sets
import std/strutils
import std/strformat

type
  gate_kind = enum
    gk_none,
    gk_input_x,
    gk_input_y,
    gk_input_z,
    gk_and,
    gk_nand,
    gk_or,
    gk_nor,
    gk_xor,
    gk_not,
    gk_const_0,
    gk_const_1,

  witness = object
    gate_kind: gate_kind
    left_operand: uint8
    right_operand: uint8

const
  unreached_cost = high(int)
  input_x_tt: uint8 = 0b11110000'u8
  input_y_tt: uint8 = 0b11001100'u8
  input_z_tt: uint8 = 0b10101010'u8
  truth_mask: uint8 = 0xFF'u8

proc is_commutative(gate_kind: gate_kind): bool =
  case gate_kind
  of gk_and, gk_or, gk_nand, gk_nor, gk_xor: true
  else: false

proc eval_binary_gate(gate_kind: gate_kind, left_tt, right_tt: uint8): uint8 =
  case gate_kind
  of gk_and: left_tt and right_tt
  of gk_nand: (not (left_tt and right_tt)) and truth_mask
  of gk_or: left_tt or right_tt
  of gk_nor: (not (left_tt or right_tt)) and truth_mask
  of gk_xor: left_tt xor right_tt
  else:
    raise new_exception(ValueError, "not a binary gate: " & $gate_kind)

proc eval_unary_gate(gate_kind: gate_kind, operand_tt: uint8): uint8 =
  case gate_kind
  of gk_not: (not operand_tt) and truth_mask
  else:
    raise new_exception(ValueError, "not a unary gate: " & $gate_kind)

proc signal_label(truth_table: uint8): string =
  if truth_table == input_z_tt: "Z"
  elif truth_table == input_y_tt: "Y"
  elif truth_table == input_x_tt: "X"
  elif truth_table == 0'u8: "0"
  elif truth_table == 0xFF'u8: "1"
  else: "0b" & to_bin(int(truth_table), 8)

proc is_primary(gate_kind: gate_kind): bool =
  gate_kind in {gk_none, gk_input_x, gk_input_y, gk_input_z, gk_const_0, gk_const_1}

proc collect_used_gates(
  target_tt: uint8,
  witness: array[256, witness],
  used: var HashSet[uint8],
) =
  let step = witness[int(target_tt)]
  if is_primary(step.gate_kind):
    return

  if target_tt in used:
    return
  used.incl target_tt

  case step.gate_kind
  of gk_not:
    collect_used_gates(step.left_operand, witness, used)
  else:
    collect_used_gates(step.left_operand, witness, used)
    collect_used_gates(step.right_operand, witness, used)

proc shared_gate_cost(
  outputs: open_array[uint8],
  witness: array[256, witness],
): int =
  var used = init_hash_set[uint8]()
  for output_tt in outputs:
    collect_used_gates(output_tt, witness, used)
  used.len

proc format_witness(
  target_tt: uint8,
  witness: array[256, witness],
  max_depth: int = 64,
  depth: int = 0,
): string =
  if depth >= max_depth:
    return "<depth>"

  let step = witness[int(target_tt)]
  case step.gate_kind
  of gk_input_x, gk_input_y, gk_input_z, gk_none, gk_const_0, gk_const_1:
    signal_label(target_tt)

  of gk_not:
    "NOT(" & format_witness(step.left_operand, witness, max_depth, depth + 1) & ")"

  of gk_and:
    "AND(" &
      format_witness(step.left_operand, witness, max_depth, depth + 1) & ", " &
      format_witness(step.right_operand, witness, max_depth, depth + 1) & ")"

  of gk_nand:
    "NAND(" &
      format_witness(step.left_operand, witness, max_depth, depth + 1) & ", " &
      format_witness(step.right_operand, witness, max_depth, depth + 1) & ")"

  of gk_or:
    "OR(" &
      format_witness(step.left_operand, witness, max_depth, depth + 1) & ", " &
      format_witness(step.right_operand, witness, max_depth, depth + 1) & ")"

  of gk_nor:
    "NOR(" &
      format_witness(step.left_operand, witness, max_depth, depth + 1) & ", " &
      format_witness(step.right_operand, witness, max_depth, depth + 1) & ")"

  of gk_xor:
    "XOR(" &
      format_witness(step.left_operand, witness, max_depth, depth + 1) & ", " &
      format_witness(step.right_operand, witness, max_depth, depth + 1) & ")"

proc optimize_logic[num_outputs: static int](
  outputs: array[num_outputs, uint8]
) =
  var best_cost: array[256, int]
  for i in 0 .. high(best_cost):
    best_cost[i] = unreached_cost

  var witness: array[256, witness]
  for i in 0 .. high(witness):
    witness[i] = witness(gate_kind: gk_none, left_operand: 0'u8, right_operand: 0'u8)

  var frontiers: seq[HashSet[uint8]] = @[]
  frontiers.add init_hash_set[uint8]()

  for (base_tt, base_kind) in [
    (input_x_tt, gk_input_x),
    (input_y_tt, gk_input_y),
    (input_z_tt, gk_input_z),
    (0x00'u8, gk_const_0),
    (0xFF'u8, gk_const_1),
  ]:
    frontiers[0].incl base_tt
    best_cost[int(base_tt)] = 0
    witness[int(base_tt)] = witness(gate_kind: base_kind)

  var remaining_outputs = init_hash_set[uint8]()
  for output_tt in outputs:
    remaining_outputs.incl output_tt
  for base_tt in frontiers[0]:
    if base_tt in remaining_outputs:
      remaining_outputs.excl base_tt

  let binary_gate_kinds: array[2, gate_kind] = [gk_nand, gk_xor]
  let unary_gate_kinds: array[0, gate_kind] = []

  var total_cost = 1
  while remaining_outputs.len > 0:
    frontiers.add init_hash_set[uint8]()
    do_assert frontiers.len == total_cost + 1

    for unary_gate in unary_gate_kinds:
      for operand_tt in frontiers[total_cost - 1]:
        let result_tt = eval_unary_gate(unary_gate, operand_tt)
        if best_cost[int(result_tt)] != unreached_cost:
          continue

        best_cost[int(result_tt)] = total_cost
        witness[int(result_tt)] = witness(
          gate_kind: unary_gate,
          left_operand: operand_tt,
          right_operand: 0'u8
        )
        frontiers[total_cost].incl result_tt
        if result_tt in remaining_outputs:
          remaining_outputs.excl result_tt

    for binary_gate in binary_gate_kinds:
      let commutative = is_commutative(binary_gate)

      for left_cost in 0 .. (total_cost - 1):
        let right_cost = (total_cost - 1) - left_cost

        if commutative and left_cost > right_cost:
          continue

        for left_tt in frontiers[left_cost]:
          for right_tt in frontiers[right_cost]:
            if commutative and left_cost == right_cost and left_tt > right_tt:
              continue

            let result_tt = eval_binary_gate(binary_gate, left_tt, right_tt)
            if best_cost[int(result_tt)] != unreached_cost:
              continue

            best_cost[int(result_tt)] = total_cost
            witness[int(result_tt)] = witness(
              gate_kind: binary_gate,
              left_operand: left_tt,
              right_operand: right_tt
            )
            frontiers[total_cost].incl result_tt
            if result_tt in remaining_outputs:
              remaining_outputs.excl result_tt

    inc total_cost

  echo "Solved."
  for output_tt in outputs:
    let cost = best_cost[int(output_tt)]
    echo signal_label(output_tt), "  cost=", cost, "  expr=", format_witness(output_tt, witness)

  let total_shared_cost = shared_gate_cost(outputs, witness)
  echo "Total gates needed=", total_shared_cost

  var used_nodes = init_hash_set[uint8]()
  for output_tt in outputs:
    collect_used_gates(output_tt, witness, used_nodes)

  var used_list: seq[uint8] = @[]
  for tt in used_nodes:
    used_list.add tt

  used_list.sort(proc (x, y: uint8): int =
    let cx = best_cost[int(x)]
    let cy = best_cost[int(y)]
    if cx != cy: cmp(cx, cy) else: cmp(int(x), int(y))
  )

  echo "Unique gate nodes:"
  for tt in used_list:
    echo "  ", signal_label(tt), "  gate=", witness[int(tt)].gate_kind,
         "  expr=", format_witness(tt, witness)

type
  seven_seg = enum
    seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g, seg_dp

const
  seg_a_bit = 1'u8 shl ord(seg_a)
  seg_b_bit = 1'u8 shl ord(seg_b)
  seg_c_bit = 1'u8 shl ord(seg_c)
  seg_d_bit = 1'u8 shl ord(seg_d)
  seg_e_bit = 1'u8 shl ord(seg_e)
  seg_f_bit = 1'u8 shl ord(seg_f)
  seg_g_bit = 1'u8 shl ord(seg_g)
  seg_dp_bit = 1'u8 shl ord(seg_dp)

  digit_mask: array[10, uint8] = [
    (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit),
    (seg_b_bit or seg_c_bit),
    (seg_a_bit or seg_b_bit or seg_d_bit or seg_e_bit or seg_g_bit),
    (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_g_bit),
    (seg_b_bit or seg_c_bit or seg_f_bit or seg_g_bit),
    (seg_a_bit or seg_c_bit or seg_d_bit or seg_f_bit or seg_g_bit),
    (seg_a_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit or seg_g_bit),
    (seg_a_bit or seg_b_bit or seg_c_bit),
    (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit or seg_g_bit),
    (seg_a_bit or seg_b_bit or seg_c_bit or seg_f_bit or seg_g_bit),
  ]

proc char_to_seg_mask(ch: char): uint8 =
  if ch >= '0' and ch <= '9':
    return digit_mask[ord(ch) - ord('0')]
  if ch == '-':
    return seg_g_bit
  0'u8

proc birthday_to_sevenseg_outputs*(month, day, year: int): array[8, uint8] =
  do_assert month in 1..12
  do_assert day in 1..31
  do_assert year >= 0

  let yy = year mod 100
  let text = &"{month:02}-{day:02}-{yy:02}"

  var outputs: array[8, uint8]
  for position, ch in text:
    let mask = char_to_seg_mask(ch)
    for seg in seven_seg:
      if (mask and (1'u8 shl ord(seg))) != 0:
        outputs[ord(seg)] = outputs[ord(seg)] or (1'u8 shl position)

  outputs

proc main() =
  let start = get_mono_time()
  let outs = birthday_to_sevenseg_outputs(6, 22, 2009)
  for i, v in outs:
    echo seven_seg(i), " = 0b", to_bin(int(v), 8)
  optimize_logic outs

  let finish = get_mono_time()
  echo "Fully took ", in_milliseconds(finish - start), "ms"
  
  # optimize_logic [
  #   0b01011011'u8
  # ]
main()
