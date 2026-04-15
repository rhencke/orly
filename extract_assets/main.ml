(** extract_assets — Rocq-verified asset extraction for q3dm1.

    Pure manifest logic (wanted, safe_path, validate_manifest) comes
    from Rocq via OCaml extraction.  I/O, ZIP/gzip/tar parsing, and
    the CLI live here in the OCaml driver. *)

(* ------------------------------------------------------------------ *)
(* Rocq char-list <-> OCaml string conversion                          *)
(* ------------------------------------------------------------------ *)

let string_of_charlist (cl : char list) : string =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

let charlist_of_string (s : string) : char list =
  List.init (String.length s) (String.get s)

(* ------------------------------------------------------------------ *)
(* File-system helpers                                                 *)
(* ------------------------------------------------------------------ *)

let read_file (path : string) : bytes =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let len = in_channel_length ic in
    let buf = Bytes.create len in
    really_input ic buf 0 len;
    buf)

(** Recursively create directories. *)
let rec mkdir_p (dir : string) : unit =
  if Sys.file_exists dir then ()
  else begin
    mkdir_p (Filename.dirname dir);
    (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
  end

let write_file (path : string) (data : string) : unit =
  mkdir_p (Filename.dirname path);
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    output_string oc data)

(* ------------------------------------------------------------------ *)
(* Installer format detection and pak0 extraction                      *)
(* ------------------------------------------------------------------ *)

(** Linux .sh installer: shell header + gzip'd tar containing pak0.pk3 *)
let pak0_from_sh (data : bytes) (name : string) : bytes =
  (* Find gzip magic bytes *)
  let len = Bytes.length data in
  let rec find_gzip off =
    if off + 1 >= len then
      failwith (Printf.sprintf "no gzip payload found in %s" name)
    else if Bytes.get data off = '\x1f' && Bytes.get data (off+1) = '\x8b'
    then off
    else find_gzip (off + 1)
  in
  let gz_off = find_gzip 0 in
  let gz_payload = Bytes.sub_string data gz_off (len - gz_off) in
  Printf.printf "Decompressing gzip payload from %s (offset %d)...\n%!" name gz_off;
  let tar_data = Gzip_reader.decompress_gzip gz_payload in
  Printf.printf "Finding pak0.pk3 in tar archive (%d bytes)...\n%!" (String.length tar_data);
  let pak0 = Tar_reader.find_pak0 (Bytes.of_string tar_data) in
  Printf.printf "Found pak0.pk3 (%d bytes) inside %s\n%!" (Bytes.length pak0) name;
  pak0

(** Windows .exe installer: try as ZIP, look for demoq3/pak0.pk3 *)
let pak0_from_exe (data : bytes) (name : string) : bytes =
  let entries = Zip_reader.read_central_directory data in
  let pak0_entry =
    List.find_opt (fun (e : Zip_reader.entry) ->
      let norm = String.lowercase_ascii e.filename in
      let norm = String.map (fun c -> if c = '\\' then '/' else c) norm in
      String.length norm >= 17
      && (let suffix = "demoq3/pak0.pk3" in
          String.length norm >= String.length suffix
          && String.sub norm (String.length norm - String.length suffix) (String.length suffix) = suffix)
    ) entries
  in
  match pak0_entry with
  | Some entry ->
    Printf.printf "Found pak0.pk3 at %S inside %s\n%!" entry.filename name;
    let contents = Zip_reader.read_entry_data data entry in
    Bytes.of_string contents
  | None ->
    failwith (Printf.sprintf
      "cannot automatically unpack pak0.pk3 from %s\n\n\
       The Windows installer uses a Cabinet-based format that requires\n\
       an external tool.  Options:\n\n\
         On Windows — run the installer, then pass pak0.pk3 directly:\n\
           extract_assets \"C:\\\\...\\\\demoq3\\\\pak0.pk3\"\n\n\
         On Linux with 7z installed:\n\
           7z e Q3ADemo.exe demoq3/pak0.pk3 -o/tmp/q3\n\
           extract_assets /tmp/q3/pak0.pk3\n\n\
         Or extract pak0.pk3 by any means and pass the path directly."
      name)

(** Open pak0.pk3 data from whatever source format the user provided. *)
let open_pak0 (path : string) : bytes =
  let data = read_file path in
  let name = Filename.basename path in
  let ext = String.lowercase_ascii (Filename.extension path) in
  match ext with
  | ".sh" -> pak0_from_sh data name
  | ".exe" -> pak0_from_exe data name
  | ".bin" ->
    failwith (Printf.sprintf
      "automatic extraction from macOS .bin installers is not supported.\n\n\
       Run the installer on macOS to install the demo, then locate pak0.pk3\n\
       (typically at <install dir>/demoq3/pak0.pk3) and pass it directly:\n\
           extract_assets /path/to/demoq3/pak0.pk3")
  | _ -> data  (* .pk3 or unrecognised — try directly as ZIP *)

(* ------------------------------------------------------------------ *)
(* JSON manifest                                                        *)
(* ------------------------------------------------------------------ *)

(** Write manifest.json to the output directory listing all extracted
    asset paths as a sorted JSON array.  The browser fetches this first
    so it knows what files to load without a hardcoded path list. *)
let write_manifest (output : string) (paths : string list) : unit =
  let buf = Buffer.create (List.length paths * 40) in
  Buffer.add_string buf "[\n";
  let n = List.length paths in
  List.iteri (fun i s ->
    Buffer.add_string buf "  \"";
    String.iter (fun c ->
      match c with
      | '"'  -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | c    -> Buffer.add_char buf c
    ) s;
    Buffer.add_char buf '"';
    if i < n - 1 then Buffer.add_char buf ',';
    Buffer.add_char buf '\n'
  ) paths;
  Buffer.add_string buf "]\n";
  let manifest_path = Filename.concat output "manifest.json" in
  write_file manifest_path (Buffer.contents buf);
  Printf.printf "Wrote %s (%d entries).\n%!" manifest_path n

(* ------------------------------------------------------------------ *)
(* Core extraction using Rocq-extracted logic                          *)
(* ------------------------------------------------------------------ *)

let rec extract (source : string) (output : string) : unit =
  if not (Sys.file_exists source) then
    failwith (Printf.sprintf "file not found: %s" source);

  let pak0_data = open_pak0 source in
  let entries = Zip_reader.read_central_directory pak0_data in

  (* Sort entries for deterministic extraction order. *)
  let entries = List.sort (fun (a : Zip_reader.entry) (b : Zip_reader.entry) ->
    String.compare a.filename b.filename) entries in

  (* Filter to wanted entries using the Rocq-extracted predicate. *)
  let to_extract = List.filter (fun (e : Zip_reader.entry) ->
    (* Skip directory entries *)
    let len = String.length e.filename in
    len > 0 && e.filename.[len - 1] <> '/'
    && Extract_assets_core.wanted (charlist_of_string e.filename)
  ) entries in

  if to_extract = [] then
    failwith "no matching assets found — is this the Quake 3 Arena Demo v1.11 pak0.pk3?";

  Printf.printf "Extracting %d files to %s/\n%!" (List.length to_extract) output;
  mkdir_p output;

  List.iter (fun (e : Zip_reader.entry) ->
    (* Path-traversal guard using Rocq-extracted safe_path *)
    if not (Extract_assets_core.safe_path (charlist_of_string e.filename)) then
      failwith (Printf.sprintf "zip entry escapes output directory: %S" e.filename);

    let dest = Filename.concat output e.filename in
    let data = Zip_reader.read_entry_data pak0_data e in
    write_file dest data
  ) to_extract;

  (* Collect extracted filenames (already sorted) for validation and manifest. *)
  let extracted_paths = List.map (fun (e : Zip_reader.entry) -> e.filename) to_extract in
  validate output extracted_paths

and validate (output : string) (paths : string list) : unit =
  (* Lowercase for the Rocq-extracted validator (case-insensitive matching). *)
  let extracted_lc = List.map String.lowercase_ascii paths in
  let extracted_cl = List.map charlist_of_string extracted_lc in

  if Extract_assets_core.validate_manifest extracted_cl then begin
    Printf.printf "Done — %d files extracted and manifest validated.\n%!" (List.length paths);
    write_manifest output paths
  end else begin
    let missing_f = Extract_assets_core.missing_files extracted_cl in
    let missing_p = Extract_assets_core.missing_prefixes extracted_cl in
    Printf.eprintf "error: the following required assets are missing from pak0.pk3:\n%!";
    List.iter (fun cl ->
      Printf.eprintf "  %s\n%!" (string_of_charlist cl)
    ) missing_f;
    List.iter (fun cl ->
      Printf.eprintf "  %s  (no files found under this directory)\n%!" (string_of_charlist cl)
    ) missing_p;
    failwith "\nThe pak0.pk3 may be from the wrong demo version or corrupt.\n\
              Expected: Quake 3 Arena Demo v1.11 (demoq3/pak0.pk3 inside the installer)."
  end

(* ------------------------------------------------------------------ *)
(* CLI                                                                 *)
(* ------------------------------------------------------------------ *)

let () =
  let usage = "extract_assets [--output DIR] <source>\n\n\
               Extract q3dm1 assets from a Quake 3 Arena Demo installer or pak0.pk3.\n\n\
               Accepted inputs: pak0.pk3 directly, the Linux .sh installer\n\
               (handled natively), or the Windows .exe installer (ZIP-compatible\n\
               versions only).  See ASSETS.md for redistribution constraints." in
  let source = ref "" in
  let output = ref "" in
  let specs = [
    "--output", Arg.Set_string output, "DIR  Destination directory (default: docs/assets)";
  ] in
  Arg.parse specs (fun s -> source := s) usage;
  if !source = "" then begin
    Arg.usage specs usage;
    exit 1
  end;
  (* Default output directory: docs/assets relative to the binary or CWD *)
  if !output = "" then
    output := Filename.concat (Sys.getcwd ()) "docs/assets";
  try
    extract !source !output
  with Failure msg ->
    Printf.eprintf "error: %s\n%!" msg;
    exit 1
