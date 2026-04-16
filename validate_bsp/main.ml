(** Standalone validator for the extracted BSP parser.

    Builds a synthetic minimal BSP in memory (144 bytes: valid header +
    17 empty lump entries), feeds it through the extracted parser, and
    runs the cross-lump consistency check.  Optionally accepts a real
    .bsp file path as argv.[1]. *)

open Bsp_core

(* ------------------------------------------------------------------ *)
(* Z / positive bridge                                                 *)
(* ------------------------------------------------------------------ *)

(** Build the extracted [positive] type from an OCaml int > 0. *)
let rec pos_of_int n =
  if n = 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1))
  else XO (pos_of_int (n asr 1))

(** Build the extracted [Z] type from an OCaml int. *)
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

(** Convert extracted [Z] back to OCaml int (for display). *)
let rec int_of_pos = function
  | XH -> 1
  | XO p -> 2 * int_of_pos p
  | XI p -> 2 * int_of_pos p + 1

let _int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_pos p
  | Zneg p -> -(int_of_pos p)

(* ------------------------------------------------------------------ *)
(* Byte-list helpers                                                   *)
(* ------------------------------------------------------------------ *)

(** Read a file into a list of extracted Z values. *)
let bytes_of_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  let zs = ref [] in
  for i = n - 1 downto 0 do
    zs := z_of_int (Char.code (Bytes.get buf i)) :: !zs
  done;
  !zs

(** Build the synthetic 144-byte minimal BSP:
    magic IBSP (0x49425350 LE) + version 46 + 17 zero lump entries. *)
let synthetic_bsp () =
  let header = [0x50; 0x53; 0x42; 0x49; 0x2E; 0x00; 0x00; 0x00] in
  let zero_entries = List.init (17 * 8) (fun _ -> 0) in
  List.map z_of_int (header @ zero_entries)

(* ------------------------------------------------------------------ *)
(* List length — the extracted list uses Rocq constructors             *)
(* ------------------------------------------------------------------ *)

let list_length xs = List.length xs

(* ------------------------------------------------------------------ *)
(* Main                                                                *)
(* ------------------------------------------------------------------ *)

let () =
  let source, bs =
    if Array.length Sys.argv > 1 then
      let path = Sys.argv.(1) in
      Printf.printf "  loading %s...\n%!" path;
      (path, bytes_of_file path)
    else begin
      Printf.printf "  no file argument — using synthetic 144-byte BSP\n%!";
      ("(synthetic)", synthetic_bsp ())
    end
  in
  Printf.printf "  input: %s (%d bytes)\n%!" source (list_length bs);
  match parse_bsp_file bs with
  | None ->
    Printf.eprintf "  FAIL: parse_bsp_file returned None\n%!";
    exit 1
  | Some bsp ->
    Printf.printf "  OK: parse_bsp_file succeeded\n%!";
    Printf.printf "    entities:     %d\n%!" (list_length (bf_entities bsp));
    Printf.printf "    textures:     %d\n%!" (list_length (bf_textures bsp));
    Printf.printf "    planes:       %d\n%!" (list_length (bf_planes bsp));
    Printf.printf "    nodes:        %d\n%!" (list_length (bf_nodes bsp));
    Printf.printf "    leaves:       %d\n%!" (list_length (bf_leaves bsp));
    Printf.printf "    leaf_faces:   %d\n%!" (list_length (bf_leaf_faces bsp));
    Printf.printf "    leaf_brushes: %d\n%!" (list_length (bf_leaf_brushes bsp));
    Printf.printf "    models:       %d\n%!" (list_length (bf_models bsp));
    Printf.printf "    brushes:      %d\n%!" (list_length (bf_brushes bsp));
    Printf.printf "    brush_sides:  %d\n%!" (list_length (bf_brush_sides bsp));
    Printf.printf "    vertexes:     %d\n%!" (list_length (bf_vertexes bsp));
    Printf.printf "    mesh_verts:   %d\n%!" (list_length (bf_mesh_verts bsp));
    Printf.printf "    effects:      %d\n%!" (list_length (bf_effects bsp));
    Printf.printf "    lightmaps:    %d\n%!" (list_length (bf_lightmaps bsp));
    let valid = bsp_cross_lump_valid bsp in
    Printf.printf "    cross-lump valid: %b\n%!" valid;
    Printf.printf "  PASS: extracted BSP parser works end-to-end\n%!";
    exit 0
