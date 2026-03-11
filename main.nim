import std/parseopt
import std/strutils
import std/strformat

import optimizer

type
  SevenSeg = enum
    seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g, seg_dp

const
  seg_a_bit = 1'u8 shl ord(seg_a)
  seg_b_bit = 1'u8 shl ord(seg_b)
  seg_c_bit = 1'u8 shl ord(seg_c)
  seg_d_bit = 1'u8 shl ord(seg_d)
  seg_e_bit = 1'u8 shl ord(seg_e)
  seg_f_bit = 1'u8 shl ord(seg_f)
  seg_g_bit = 1'u8 shl ord(seg_g)

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

proc usage() =
  echo "Usage: gate --birthday MM-DD-YYYY [--not] [--and] [--nand] [--or] [--nor] [--xor]"
  echo "If no gate flags are passed, all gates are enabled."

proc char_to_seg_mask(ch: char): uint8 =
  if ch >= '0' and ch <= '9':
    return digit_mask[ord(ch) - ord('0')]
  if ch == '-':
    return seg_g_bit
  0'u8

proc birthday_to_sevenseg_outputs(month, day, year: int): array[8, uint8] =
  do_assert month in 1..12
  do_assert day in 1..31
  do_assert year >= 0

  let yy = year mod 100
  let text = &"{month:02}-{day:02}-{yy:02}"

  var outputs: array[8, uint8]
  for position, ch in text:
    let mask = char_to_seg_mask(ch)
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

  let outs = birthday_to_sevenseg_outputs(parsed.month, parsed.day, parsed.year)
  for i, v in outs:
    echo SevenSeg(i), " = 0b", to_bin(int(v), 8)

  fully_optimize_logic(
    @outs,
    enable_not = enable_not,
    enable_and = enable_and,
    enable_nand = enable_nand,
    enable_or = enable_or,
    enable_nor = enable_nor,
    enable_xor = enable_xor,
  )

main()
