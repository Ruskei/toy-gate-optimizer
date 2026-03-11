import std/parseopt
import std/strutils
import std/strformat
import std/times
import std/monotimes

import optimizer

type
  SevenSeg = enum
    seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g, seg_dp
  StyleCandidate = object
    outs: array[8, uint8]
    one_uses_ef: bool
    six_has_a: bool
    nine_has_d: bool
    lit_count: int
    variant_id: int
    run: OptimizeRun

const
  seg_a_bit = 1'u8 shl ord(seg_a)
  seg_b_bit = 1'u8 shl ord(seg_b)
  seg_c_bit = 1'u8 shl ord(seg_c)
  seg_d_bit = 1'u8 shl ord(seg_d)
  seg_e_bit = 1'u8 shl ord(seg_e)
  seg_f_bit = 1'u8 shl ord(seg_f)
  seg_g_bit = 1'u8 shl ord(seg_g)

  digit_0_mask = (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit)
  digit_1_bc_mask = (seg_b_bit or seg_c_bit)
  digit_1_ef_mask = (seg_e_bit or seg_f_bit)
  digit_2_mask = (seg_a_bit or seg_b_bit or seg_d_bit or seg_e_bit or seg_g_bit)
  digit_3_mask = (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_g_bit)
  digit_4_mask = (seg_b_bit or seg_c_bit or seg_f_bit or seg_g_bit)
  digit_5_mask = (seg_a_bit or seg_c_bit or seg_d_bit or seg_f_bit or seg_g_bit)
  digit_6_with_a_mask = (seg_a_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit or seg_g_bit)
  digit_6_without_a_mask = (seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit or seg_g_bit)
  digit_7_mask = (seg_a_bit or seg_b_bit or seg_c_bit)
  digit_8_mask = (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_e_bit or seg_f_bit or seg_g_bit)
  digit_9_with_d_mask = (seg_a_bit or seg_b_bit or seg_c_bit or seg_d_bit or seg_f_bit or seg_g_bit)
  digit_9_without_d_mask = (seg_a_bit or seg_b_bit or seg_c_bit or seg_f_bit or seg_g_bit)

proc usage() =
  echo "Usage: gate --birthday MM-DD-YYYY [--not] [--and] [--nand] [--or] [--nor] [--xor]"
  echo "If no gate flags are passed, all gates are enabled."

proc char_to_seg_mask(
  ch: char,
  one_uses_ef: bool,
  six_has_a: bool,
  nine_has_d: bool,
): uint8 =
  case ch
  of '0':
    digit_0_mask
  of '1':
    if one_uses_ef: digit_1_ef_mask else: digit_1_bc_mask
  of '2':
    digit_2_mask
  of '3':
    digit_3_mask
  of '4':
    digit_4_mask
  of '5':
    digit_5_mask
  of '6':
    if six_has_a: digit_6_with_a_mask else: digit_6_without_a_mask
  of '7':
    digit_7_mask
  of '8':
    digit_8_mask
  of '9':
    if nine_has_d: digit_9_with_d_mask else: digit_9_without_d_mask
  of '-':
    seg_g_bit
  else:
    0'u8

proc birthday_to_sevenseg_outputs(
  month, day, year: int,
  one_uses_ef: bool,
  six_has_a: bool,
  nine_has_d: bool,
): array[8, uint8] =
  do_assert month in 1..12
  do_assert day in 1..31
  do_assert year >= 0

  let yy = year mod 100
  let text = &"{month:02}-{day:02}-{yy:02}"

  var outputs: array[8, uint8]
  for position, ch in text:
    let mask = char_to_seg_mask(ch, one_uses_ef, six_has_a, nine_has_d)
    for seg in SevenSeg:
      if (mask and (1'u8 shl ord(seg))) != 0:
        outputs[ord(seg)] = outputs[ord(seg)] or (1'u8 shl position)

  outputs

proc parse_birthday(value: string): tuple[ok: bool, month: int, day: int, year: int] =
  let normalized = value.replace("/", "-")
  let parts = normalized.split("-")
  if parts.len != 3:
    return (false, 0, 0, 0)

  try:
    let month = parse_int(parts[0])
    let day = parse_int(parts[1])
    let year = parse_int(parts[2])
    if month notin 1..12 or day notin 1..31 or year < 0:
      return (false, 0, 0, 0)
    (true, month, day, year)
  except ValueError:
    (false, 0, 0, 0)

proc count_set_bits(value: uint8): int =
  var bits = value
  while bits != 0:
    result += int(bits and 1'u8)
    bits = bits shr 1

proc total_lit_count(outputs: array[8, uint8]): int =
  for output in outputs:
    result += count_set_bits(output)

proc is_better_candidate(a, b: StyleCandidate): bool =
  if a.run.min_gates != b.run.min_gates:
    return a.run.min_gates < b.run.min_gates
  if a.lit_count != b.lit_count:
    return a.lit_count > b.lit_count
  a.variant_id < b.variant_id

proc main() =
  var birthday_arg = ""
  var enable_not = false
  var enable_and = false
  var enable_nand = false
  var enable_or = false
  var enable_nor = false
  var enable_xor = false
  var gate_flag_set = false

  for kind, key, value in getopt():
    case kind
    of cmd_long_option, cmd_short_option:
      case key
      of "birthday", "b":
        birthday_arg = value
      of "not":
        enable_not = true
        gate_flag_set = true
      of "and":
        enable_and = true
        gate_flag_set = true
      of "nand":
        enable_nand = true
        gate_flag_set = true
      of "or":
        enable_or = true
        gate_flag_set = true
      of "nor":
        enable_nor = true
        gate_flag_set = true
      of "xor":
        enable_xor = true
        gate_flag_set = true
      of "help", "h":
        usage()
        quit(0)
      else:
        usage()
        quit("Unknown option: --" & key, 1)
    of cmd_argument:
      if birthday_arg.len == 0:
        birthday_arg = key
      else:
        usage()
        quit("Unexpected argument: " & key, 1)
    of cmd_end:
      discard

  if birthday_arg.len == 0:
    usage()
    quit("Missing required birthday. Use --birthday MM-DD-YYYY.", 1)

  let parsed = parse_birthday(birthday_arg)
  if not parsed.ok:
    usage()
    quit("Invalid birthday: " & birthday_arg & ". Expected MM-DD-YYYY.", 1)

  if not gate_flag_set:
    enable_not = true
    enable_and = true
    enable_nand = true
    enable_or = true
    enable_nor = true
    enable_xor = true

  var best_candidate: StyleCandidate
  var has_best_candidate = false
  var variant_id = 0
  let yy = parsed.year mod 100
  let birthday_text = &"{parsed.month:02}-{parsed.day:02}-{yy:02}"

  var one_styles: seq[bool] = @[false]
  if birthday_text.contains('1'):
    one_styles.add true

  var six_styles: seq[bool] = @[false]
  if birthday_text.contains('6'):
    six_styles.add true

  var nine_styles: seq[bool] = @[false]
  if birthday_text.contains('9'):
    nine_styles.add true

  let start = get_mono_time()

  for one_uses_ef in one_styles:
    for six_has_a in six_styles:
      for nine_has_d in nine_styles:
        let outs = birthday_to_sevenseg_outputs(
          parsed.month,
          parsed.day,
          parsed.year,
          one_uses_ef,
          six_has_a,
          nine_has_d,
        )
        let run = capture_optimize_run(
          @outs,
          enable_not = enable_not,
          enable_and = enable_and,
          enable_nand = enable_nand,
          enable_or = enable_or,
          enable_nor = enable_nor,
          enable_xor = enable_xor,
        )
        let candidate = StyleCandidate(
          outs: outs,
          one_uses_ef: one_uses_ef,
          six_has_a: six_has_a,
          nine_has_d: nine_has_d,
          lit_count: total_lit_count(outs),
          variant_id: variant_id,
          run: run,
        )
        if not has_best_candidate or is_better_candidate(candidate, best_candidate):
          best_candidate = candidate
          has_best_candidate = true
        inc variant_id

  let finish = get_mono_time()

  for i, v in best_candidate.outs:
    echo SevenSeg(i), " = 0b", to_bin(int(v), 8)

  print_optimize_run(@(best_candidate.outs), best_candidate.run)
  echo "Total optiimization time=", in_milliseconds(finish - start), "ms"

main()
