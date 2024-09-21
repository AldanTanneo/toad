let version = "0.1.0"

let output_file =
  if Sys.unix then ref "a.out" else failwith "Not ported to non-unix"

let input_files = ref []
let cflags = ref []
let compiler = ref "gcc"

let parse () =
  let usage =
    Printf.sprintf
      "This is the Toad Compiler, version %s.\nUsage: %s [file1] [file2] ...\n"
      version
      (Filename.basename Sys.argv.(0))
  in
  let add_input_file file =
    if
      not
        (Toad.Utils.is_valid_identifier
           (Filename.remove_extension (Filename.basename file)))
    then raise (Arg.Bad "Input file names must be valid module names")
    else input_files := file :: !input_files
  in
  let speclist =
    Arg.align
      [
        ("-o", Arg.Set_string output_file, "<file> Set output file name");
        ( "-C",
          Arg.String (fun flag -> cflags := flag :: !cflags),
          "<flag> Set flags for the C compiler" );
        ( "--compiler",
          Arg.Set_string compiler,
          "<command> Set the C compiler used" );
        ( "--version",
          Arg.Unit
            (fun () ->
              Printf.printf "toadc %s\n" version;
              exit 0),
          " Print version and exit" );
        ( "--",
          Arg.Rest (fun flag -> cflags := flag :: !cflags),
          " Interpret the rest of the arguments as C compiler flags" );
      ]
  in
  Arg.parse speclist add_input_file usage;
  if !input_files = [] then (
    Arg.usage speclist usage;
    exit 1)
  else input_files := List.rev !input_files;
  cflags := List.rev !cflags
