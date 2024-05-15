open Cmdliner
open Caesar

let encrypt msg k =
  match text_of_string msg with
  | Some t -> Printf.printf "%s\n" (string_of_text (encrypt t k))
  | None ->
      Printf.printf
        "ERROR: Please enter string consisting only of uppercase ASCII letters\n"

let () =
  let message =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~doc:"Message to encrypt/decrypt" ~docv:"MSG")
  in
  let shift =
    Arg.(
      required & pos 1 (some int) None & info [] ~doc:"Shift amount" ~docv:"K")
  in
  let info = Cmd.info "vericaesar" in
  let cmd = Cmd.v info Term.(const encrypt $ message $ shift) in
  exit (Cmd.eval cmd)
