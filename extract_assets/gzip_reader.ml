(** Gzip decompression using [decompress.gz]. *)

let decompress_gzip (data : string) : string =
  let src_off = ref 0 in
  let dst = Buffer.create (String.length data * 2) in
  let i = De.bigstring_create 4096 in
  let o = De.bigstring_create 4096 in
  let refill buf =
    let available = min 4096 (String.length data - !src_off) in
    for j = 0 to available - 1 do
      Bigarray.Array1.set buf j (String.get data (!src_off + j))
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
  match Gz.Higher.uncompress ~refill ~flush i o with
  | Ok _gz_metadata -> Buffer.contents dst
  | Error (`Msg msg) -> failwith ("gzip decompression failed: " ^ msg)
