let return x = Some x
let ( let* ) x f = Option.bind x f

let ( and* ) a b =
  match (a, b) with
  | None, _ | _, None -> None
  | Some v1, Some v2 -> Some (v1, v2)

let ( let+ ) x f = Option.map f x

let ( and+ ) a b =
  match (a, b) with
  | None, _ | _, None -> None
  | Some v1, Some v2 -> Some (v1, v2)

let zip a b = List.map2 (fun x y -> (x, y)) a b
let is_digit c = c >= '0' && c <= '9'

let unique_string =
  let map = Hashtbl.create 1 in
  fun x ->
    let n = String.length x in
    let x = if String.starts_with ~prefix:"$tmp" x then "$tmp" else x in
    let x =
      if String.starts_with ~prefix:"$" x then String.sub x 1 (n - 1) else x
    in
    let cpt = Option.value ~default:0 (Hashtbl.find_opt map x) in
    Hashtbl.replace map x (cpt + 1);

    let n = String.length x in
    if x <> "" && cpt = 0 && not (is_digit (String.get x (n - 1))) then x
    else x ^ "_" ^ string_of_int cpt

let reverse_unique x =
  let n = String.length x in
  if n > 1 && is_digit (String.get x (n - 1)) then
    let n = String.rindex_from x (n - 1) '_' in
    String.sub x 0 n
  else x

let is_valid_identifier x =
  String.length x <> 0
  && (not (is_digit x.[0]))
  && String.for_all
       (fun c ->
         ('a' <= c && c <= 'z')
         || ('A' <= c && c <= 'Z')
         || is_digit c || c = '_')
       x

module Vec = struct
  type 'a t = { mutable data : 'a array; mutable len : int }

  let len vec = vec.len
  let cap vec = Array.length vec.data
  let create () = { data = [||]; len = 0 }
  let make n elt = { data = Array.make n elt; len = n }

  let push vec elt =
    if vec.len = Array.length vec.data then (
      let arr =
        Array.make (if vec.len = 0 then 4 else 2 * vec.len) (Obj.magic 0)
      in
      for i = 0 to vec.len - 1 do
        arr.(i) <- vec.data.(i)
      done;
      vec.data <- arr);
    vec.data.(vec.len) <- elt;
    vec.len <- vec.len + 1

  let pop vec =
    if vec.len = 0 then raise (Invalid_argument "Cannot pop from empty vec")
    else (
      vec.len <- vec.len - 1;
      vec.data.(vec.len))

  let get vec i =
    if i < 0 || vec.len <= i then
      raise (Invalid_argument "Vec index out of bounds")
    else vec.data.(i)
end
