(** OCaml driver for the pak0.pk3 asset extractor.

    Pure logic (manifest, [wanted_lc] predicate) lives in
    [Extract_assets_core], extracted from [theories/ExtractAssets.v].
    This module handles all I/O: installer detection, gzip/tar unwrapping,
    ZIP extraction, and manifest validation.

    Usage:
      extract-assets [--output DIR] <source>

    <source> may be:
      pak0.pk3                — pak0.pk3 directly
      linuxq3ademo-*.sh       — Linux Loki installer (handled natively)
      Q3ADemo.exe             — Windows installer (ZIP-compatible only)
      MacQuake3Demo.bin       — macOS installer (manual extraction required)

    See ASSETS.md for redistribution constraints. *)

(* ---------------------------------------------------------------------------
   Helpers
   --------------------------------------------------------------------------- *)

let die fmt =
  Printf.ksprintf (fun s -> Printf.eprintf "%s\n%!" s; exit 1) fmt

let read_file_bytes path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  buf

(** Drain a [Gzip.in_channel] into a fresh [Bytes.t]. *)
let gzip_read_all gz_ic =
  let buf = Buffer.create (16 * 1024 * 1024) in
  let block = Bytes.create 65536 in
  (try
     while true do
       let n = Gzip.input gz_ic block 0 (Bytes.length block) in
       if n = 0 then raise Exit;
       Buffer.add_subbytes buf block 0 n
     done
   with Exit | End_of_file -> ());
  Buffer.to_bytes buf

(** Write [data] to a temp file, pass its path to [f], remove it afterwards. *)
let with_temp_file suffix data f =
  let path = Filename.temp_file "orly_extract" suffix in
  (let oc = open_out_bin path in
   output_bytes oc data;
   close_out oc);
  Fun.protect
    ~finally:(fun () -> try Sys.remove path with _ -> ())
    (fun () -> f path)

(** Normalise backslash path separators to forward slash. *)
let normalize_slash s =
  String.concat "/" (String.split_on_char '\\' s)

(** Parse an octal string as found in tar headers. *)
let parse_octal s =
  let s =
    String.map (fun c -> if c = '\x00' then ' ' else c) s |> String.trim
  in
  if s = "" then 0 else int_of_string ("0o" ^ s)

(** [mkdir -p] using [Unix.mkdir]. *)
let mkdirp path =
  let rec aux p =
    if p = Filename.dirname p then ()
    else begin
      (try Unix.mkdir p 0o755
       with
       | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
       | Unix.Unix_error (Unix.ENOENT, _, _) ->
           aux (Filename.dirname p);
           (try Unix.mkdir p 0o755
            with Unix.Unix_error (Unix.EEXIST, _, _) -> ()))
    end
  in
  aux path

(* ---------------------------------------------------------------------------
   Safe destination path
   --------------------------------------------------------------------------- *)

(** Resolve a zip entry name to a safe destination under [output].
    Returns [None] for entries that would escape the output directory
    (path-traversal defence) or that have no usable name component. *)
let safe_dest output zip_name =
  let name = normalize_slash zip_name in
  let parts =
    String.split_on_char '/' name
    |> List.filter (fun p -> p <> "" && p <> "." && p <> "..")
  in
  match parts with
  | [] -> None
  | _ ->
    Some (List.fold_left Filename.concat output parts)

(* ---------------------------------------------------------------------------
   Minimal tar parser (in-memory — enough to locate pak0.pk3 in Loki installers)
   --------------------------------------------------------------------------- *)

(** Scan [data] for the first entry whose lowercased, slash-normalised path
    ends with ["demoq3/pak0.pk3"].  Returns the raw entry bytes or calls
    [die] if not found. *)
let find_pak0_in_tar_bytes data =
  let len = Bytes.length data in
  let pos = ref 0 in
  let target = "demoq3/pak0.pk3" in
  let tlen = String.length target in
  let found = ref None in
  (try
     while !found = None && !pos + 512 <= len do
       let hdr = !pos in
       pos := !pos + 512;
       (* Two consecutive zero blocks mark end-of-archive. *)
       let is_zero = ref true in
       for i = hdr to hdr + 511 do
         if Bytes.get_uint8 data i <> 0 then is_zero := false
       done;
       if !is_zero then raise Exit;
       (* Name field: 100 bytes at offset 0, NUL-terminated. *)
       let name_raw = Bytes.sub_string data hdr 100 in
       let name =
         match String.index_opt name_raw '\x00' with
         | Some i -> String.sub name_raw 0 i
         | None   -> name_raw
       in
       (* Size field: 12 octal bytes at offset 124. *)
       let size = parse_octal (Bytes.sub_string data (hdr + 124) 12) in
       let name_lc = String.lowercase_ascii (normalize_slash name) in
       let nlen = String.length name_lc in
       let is_target =
         name_lc = target
         || ( nlen > tlen
              && String.sub name_lc (nlen - tlen) tlen = target
              && (let c = name_lc.[nlen - tlen - 1] in c = '/' || c = '\\') )
       in
       let blocks = (size + 511) / 512 in
       if is_target then begin
         Printf.printf "Found pak0.pk3 at %s\n%!" name;
         if !pos + size <= len then
           found := Some (Bytes.sub data !pos size)
         else
           die "error: tar entry for pak0.pk3 is truncated in installer"
       end;
       pos := !pos + blocks * 512
     done
   with Exit -> ());
  match !found with
  | Some d -> d
  | None   ->
    die
      "error: demoq3/pak0.pk3 not found in installer\n\
       Make sure this is the Quake 3 Arena Demo v1.11 Linux installer."

(* ---------------------------------------------------------------------------
   Installer-format detection and pak0.pk3 unwrapping
   --------------------------------------------------------------------------- *)

(** Extract pak0.pk3 from a Loki .sh installer.
    Calls [f] with a temporary path to pak0.pk3; cleans up afterwards. *)
let with_pak0_from_sh installer_path f =
  let data = read_file_bytes installer_path in
  let len = Bytes.length data in
  (* Locate the gzip magic bytes (0x1f 0x8b). *)
  let gz_offset = ref (-1) in
  for i = 0 to len - 2 do
    if !gz_offset = -1
       && Bytes.get_uint8 data i = 0x1f
       && Bytes.get_uint8 data (i + 1) = 0x8b
    then gz_offset := i
  done;
  if !gz_offset = -1 then
    die
      "error: no gzip payload found in %s\n\
       Expected the Quake 3 Arena Demo Linux installer \
       (linuxq3ademo-1.11-6.x86.gz.sh)."
      installer_path;
  (* Decompress the gzip payload. *)
  let gz_slice = Bytes.sub data !gz_offset (len - !gz_offset) in
  let tar_bytes =
    with_temp_file ".gz" gz_slice (fun gz_path ->
      let gz_ic = Gzip.open_in gz_path in
      let result =
        Fun.protect
          ~finally:(fun () -> Gzip.close_in gz_ic)
          (fun () -> gzip_read_all gz_ic)
      in
      result)
  in
  let pak0_bytes = find_pak0_in_tar_bytes tar_bytes in
  with_temp_file ".pk3" pak0_bytes f

(** Try to locate pak0.pk3 inside a Windows .exe installer (ZIP-compatible
    self-extractors only).  Calls [f] with a temp path on success. *)
let with_pak0_from_exe installer_path f =
  let target = "demoq3/pak0.pk3" in
  let tlen = String.length target in
  let found_entry =
    match Zip.open_in installer_path with
    | exception _ -> None
    | zf ->
      let entry =
        List.find_opt (fun e ->
          let n = String.lowercase_ascii (normalize_slash e.Zip.filename) in
          let nlen = String.length n in
          n = target
          || ( nlen > tlen
               && String.sub n (nlen - tlen) tlen = target
               && (let c = n.[nlen - tlen - 1] in c = '/' || c = '\\') )
        ) (Zip.entries zf)
      in
      (match entry with
       | Some e ->
         Printf.printf "Found pak0.pk3 at %s inside %s\n%!"
           e.Zip.filename installer_path;
         let bytes = Bytes.of_string (Zip.read_entry zf e) in
         Zip.close_in zf;
         Some bytes
       | None ->
         Zip.close_in zf;
         None)
  in
  match found_entry with
  | Some pak0_bytes -> with_temp_file ".pk3" pak0_bytes f
  | None ->
    die
      "error: cannot automatically unpack pak0.pk3 from %s\n\n\
       The Windows installer uses a Cabinet-based format that requires\n\
       an external tool.  Options:\n\n\
       \  On Windows — run the installer, then pass pak0.pk3 directly:\n\
       \    extract-assets \"C:\\...\\demoq3\\pak0.pk3\"\n\n\
       \  On Linux with 7z installed:\n\
       \    7z e Q3ADemo.exe demoq3/pak0.pk3 -o/tmp/q3\n\
       \    extract-assets /tmp/q3/pak0.pk3\n\n\
       \  Or extract pak0.pk3 by any means and pass the path directly."
      installer_path

(** Open pak0.pk3 — routing through installer logic when needed — and call
    [f] with the path to a (possibly temporary) pk3 file. *)
let with_pak0 source f =
  let suffix =
    let b = Filename.basename source in
    match String.rindex_opt b '.' with
    | Some i ->
      String.lowercase_ascii (String.sub b i (String.length b - i))
    | None -> ""
  in
  match suffix with
  | ".sh"  -> with_pak0_from_sh source f
  | ".exe" -> with_pak0_from_exe source f
  | ".bin" ->
    die
      "error: automatic extraction from macOS .bin installers is not supported.\n\n\
       Run the installer on macOS, then locate pak0.pk3\n\
       (typically at <install dir>/demoq3/pak0.pk3) and pass it directly:\n\
       \    extract-assets /path/to/demoq3/pak0.pk3"
  | _ ->
    (* Treat as pak0.pk3 / ZIP directly. *)
    (try f source
     with Zip.Error (_, _, msg) ->
       die "error: %s is not a valid ZIP/pk3 file: %s" source msg)

(* ---------------------------------------------------------------------------
   Manifest validation
   --------------------------------------------------------------------------- *)

let validate output extracted_count =
  let missing = ref [] in
  List.iter (fun req ->
    let p = Filename.concat output req in
    if not (Sys.file_exists p && not (Sys.is_directory p)) then
      missing := req :: !missing
  ) Extract_assets_core.required_files;
  List.iter (fun pre ->
    let dir = Filename.concat output pre in
    let has_file =
      try
        Array.exists
          (fun e -> not (Sys.is_directory (Filename.concat dir e)))
          (Sys.readdir dir)
      with Sys_error _ -> false
    in
    if not has_file then
      missing :=
        (pre ^ "  (no files found under this directory)") :: !missing
  ) Extract_assets_core.required_prefixes;
  match !missing with
  | [] ->
    Printf.printf "Done — %d files extracted and manifest validated.\n"
      extracted_count
  | ms ->
    Printf.eprintf
      "error: the following required assets are missing from pak0.pk3:\n";
    List.iter (fun m -> Printf.eprintf "  %s\n" m) (List.rev ms);
    Printf.eprintf
      "\nThe pak0.pk3 may be from the wrong demo version or corrupt.\n";
    Printf.eprintf
      "Expected: Quake 3 Arena Demo v1.11 \
       (demoq3/pak0.pk3 inside the installer).\n";
    exit 1

(* ---------------------------------------------------------------------------
   Core extraction from a pak0.pk3 path
   --------------------------------------------------------------------------- *)

let extract pak0_path output =
  let zf = Zip.open_in pak0_path in
  let all_entries = Zip.entries zf in
  (* Sort entries for deterministic extraction order. *)
  let sorted =
    List.sort
      (fun a b -> String.compare a.Zip.filename b.Zip.filename)
      all_entries
  in
  let to_extract =
    List.filter (fun e ->
      not e.Zip.is_directory
      && Extract_assets_core.wanted_lc
           (String.lowercase_ascii e.Zip.filename)
    ) sorted
  in
  if to_extract = [] then begin
    Zip.close_in zf;
    die
      "error: no matching assets found — \
       is this the Quake 3 Arena Demo v1.11 pak0.pk3?"
  end;
  Printf.printf "Extracting %d files to %s/\n%!"
    (List.length to_extract) output;
  mkdirp output;
  List.iter (fun e ->
    match safe_dest output e.Zip.filename with
    | None -> ()
    | Some dest ->
      mkdirp (Filename.dirname dest);
      let data = Zip.read_entry zf e in
      let oc = open_out_bin dest in
      output_string oc data;
      close_out oc
  ) to_extract;
  let count = List.length to_extract in
  Zip.close_in zf;
  validate output count

(* ---------------------------------------------------------------------------
   Entry point
   --------------------------------------------------------------------------- *)

let usage =
  "Usage: extract-assets [--output DIR] <source>\n\n\
   <source> may be:\n\
   \  pak0.pk3                 — pak0.pk3 directly\n\
   \  linuxq3ademo-*.sh        — Linux installer (handled natively)\n\
   \  Q3ADemo.exe              — Windows installer (ZIP-compatible only)\n\n\
   See ASSETS.md for redistribution constraints."

let () =
  let output = ref "" in
  let source = ref "" in
  let spec =
    [ ( "--output"
      , Arg.String (fun s -> output := s)
      , "DIR  Destination directory (default: docs/assets)" ) ]
  in
  let set_source s =
    if !source <> "" then die "error: too many arguments";
    source := s
  in
  Arg.parse spec set_source usage;
  if !source = "" then (Arg.usage spec usage; exit 1);
  if !output = "" then output := "docs/assets";
  let source = !source and output = !output in
  if not (Sys.file_exists source) then
    die "error: file not found: %s" source;
  with_pak0 source (fun pak0_path -> extract pak0_path output)
