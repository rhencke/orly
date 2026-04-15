(** Minimal tar reader — enough to find demoq3/pak0.pk3 in a tar stream. *)

(** Parse an octal ASCII field, stopping at NUL or space. *)
let parse_octal (s : string) : int =
  let len = String.length s in
  let rec go acc i =
    if i >= len then acc
    else
      let c = Char.code s.[i] in
      if c = 0 || c = 0x20 then acc
      else go (acc * 8 + (c - 0x30)) (i + 1)
  in
  go 0 0

(** Find demoq3/pak0.pk3 inside a tar archive (as bytes).
    Returns the file contents or raises [Failure]. *)
let find_pak0 (data : bytes) : bytes =
  let len = Bytes.length data in
  let rec scan off =
    if off + 512 > len then failwith "demoq3/pak0.pk3 not found in tar archive"
    else
      (* A block of all zeros marks end of archive. *)
      let all_zero = ref true in
      for i = 0 to 511 do
        if Bytes.get data (off + i) <> '\000' then all_zero := false
      done;
      if !all_zero then failwith "demoq3/pak0.pk3 not found in tar archive"
      else
        let name_raw = Bytes.sub_string data off 100 in
        let name = match String.index_opt name_raw '\000' with
          | Some i -> String.sub name_raw 0 i
          | None -> name_raw
        in
        let size_field = Bytes.sub_string data (off + 124) 12 in
        let size = parse_octal size_field in
        (* Tar entries are padded to 512-byte blocks *)
        let data_blocks = (size + 511) / 512 in
        let name_lc = String.lowercase_ascii name in
        let name_norm = String.map (fun c -> if c = '\\' then '/' else c) name_lc in
        if String.length name_norm >= 17
           && String.ends_with ~suffix:"demoq3/pak0.pk3" name_norm then
          Bytes.sub data (off + 512) size
        else
          scan (off + 512 + data_blocks * 512)
  in
  scan 0
