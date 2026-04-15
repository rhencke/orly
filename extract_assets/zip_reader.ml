(** Minimal ZIP archive reader — reads central directory and extracts
    entries using the [decompress] library for DEFLATE.

    Only handles single-disk archives with 32-bit offsets (no ZIP64).
    Sufficient for pak0.pk3 and Quake 3 demo installers. *)

type entry = {
  filename : string;
  compression : int;  (** 0 = stored, 8 = deflated *)
  compressed_size : int;
  uncompressed_size : int;
  local_header_offset : int;
}

(* ------------------------------------------------------------------ *)
(* Binary helpers                                                      *)
(* ------------------------------------------------------------------ *)

let get_u16 buf off = Bytes.get_uint16_le buf off
let get_u32 buf off = Int32.to_int (Bytes.get_int32_le buf off)

let find_eocd (buf : bytes) : int =
  (* Scan backwards for End of Central Directory signature 0x06054b50.
     The EOCD is at least 22 bytes, and the comment can be up to 65535. *)
  let len = Bytes.length buf in
  let start = max 0 (len - 22 - 65535) in
  let rec scan off =
    if off < start then failwith "ZIP: end-of-central-directory record not found"
    else if Bytes.get buf off = '\x50'
         && Bytes.get buf (off + 1) = '\x4b'
         && Bytes.get buf (off + 2) = '\x05'
         && Bytes.get buf (off + 3) = '\x06'
    then off
    else scan (off - 1)
  in
  scan (len - 22)

(* ------------------------------------------------------------------ *)
(* Central directory parsing                                           *)
(* ------------------------------------------------------------------ *)

let read_central_directory (buf : bytes) : entry list =
  let eocd_off = find_eocd buf in
  let total_entries = get_u16 buf (eocd_off + 10) in
  let cd_offset = get_u32 buf (eocd_off + 16) in
  let rec read_entries off n acc =
    if n = 0 then List.rev acc
    else begin
      (* Central directory file header signature: 0x02014b50 *)
      if Bytes.get buf off <> '\x50' || Bytes.get buf (off+1) <> '\x4b'
         || Bytes.get buf (off+2) <> '\x01' || Bytes.get buf (off+3) <> '\x02'
      then failwith "ZIP: bad central directory entry signature"
      else
        let compression = get_u16 buf (off + 10) in
        let compressed_size = get_u32 buf (off + 20) in
        let uncompressed_size = get_u32 buf (off + 24) in
        let name_len = get_u16 buf (off + 28) in
        let extra_len = get_u16 buf (off + 30) in
        let comment_len = get_u16 buf (off + 32) in
        let local_header_offset = get_u32 buf (off + 42) in
        let filename = Bytes.sub_string buf (off + 46) name_len in
        let entry = { filename; compression; compressed_size;
                      uncompressed_size; local_header_offset } in
        read_entries (off + 46 + name_len + extra_len + comment_len) (n - 1) (entry :: acc)
    end
  in
  read_entries cd_offset total_entries []

(* ------------------------------------------------------------------ *)
(* Entry data extraction                                               *)
(* ------------------------------------------------------------------ *)

let raw_entry_data (buf : bytes) (e : entry) : string =
  (* Skip the local file header to find the compressed data. *)
  let off = e.local_header_offset in
  if Bytes.get buf off <> '\x50' || Bytes.get buf (off+1) <> '\x4b'
     || Bytes.get buf (off+2) <> '\x03' || Bytes.get buf (off+3) <> '\x04'
  then failwith ("ZIP: bad local header for " ^ e.filename)
  else
    let name_len = get_u16 buf (off + 26) in
    let extra_len = get_u16 buf (off + 28) in
    let data_off = off + 30 + name_len + extra_len in
    Bytes.sub_string buf data_off e.compressed_size

(** Inflate raw DEFLATE data using [decompress]. *)
let inflate_raw (compressed : string) (expected_size : int) : string =
  let src_off = ref 0 in
  let dst = Buffer.create expected_size in
  let i = De.bigstring_create 4096 in
  let o = De.bigstring_create 4096 in
  let w = De.make_window ~bits:15 in
  let refill buf =
    let available = min 4096 (String.length compressed - !src_off) in
    for j = 0 to available - 1 do
      Bigarray.Array1.set buf j (String.get compressed (!src_off + j))
    done;
    src_off := !src_off + available;
    available
  in
  let flush buf len =
    let tmp = Bytes.create len in
    for j = 0 to len - 1 do
      Bytes.set tmp j (Bigarray.Array1.get buf j)
    done;
    Buffer.add_bytes dst tmp
  in
  match De.Higher.uncompress ~w ~refill ~flush i o with
  | Ok () -> Buffer.contents dst
  | Error (`Msg msg) -> failwith ("DEFLATE decompression failed: " ^ msg)

let read_entry_data (buf : bytes) (e : entry) : string =
  let raw = raw_entry_data buf e in
  match e.compression with
  | 0 -> raw  (* stored *)
  | 8 -> inflate_raw raw e.uncompressed_size  (* deflated *)
  | m -> failwith (Printf.sprintf "ZIP: unsupported compression method %d for %s" m e.filename)
