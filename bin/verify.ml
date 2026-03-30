open Why3
open Ptree_helpers
open Infv.Tools
open Infv.Examples
module Log = Dolog.Log

let type_check env path filename mlw_file =
  try Typing.type_mlw_file env path filename mlw_file with
  | e ->
     Log.error "Type check error: %s: %s" filename (Printexc.to_string e);
     exit 1

let build_mods env name decls =
  let use_int = use ~import:false (["int";"EuclideanDivision"]) in (* 使いたいライブラリによって変更 *)
  let use_ref = use ~import:false (["ref";"Ref"]) in
  let mlw_file = Ptree.Modules [(ident name, use_int::use_ref::decls)] in
  Log.debug "%s" begin
      Format.asprintf "@[Construct Ptree Success:@\n%a@]@."
        (Mlw_printer.pp_mlw_file ~attr:true) mlw_file
    end;
  let mods = type_check env [] (name ^ ".mlw") mlw_file in
  mods

let extract_tasks mods : Task.task list =
  (* mods はモジュール名から型付きモジュールへのマップ *)
  Wstdlib.Mstr.fold (fun _ m acc ->
    (* 各モジュールの mod_theory からタスクを分割して抽出 *)
    let tasks = Task.split_theory m.Pmodule.mod_theory None None in
    List.rev_append tasks acc
  ) mods []

let verify name expr =
  (* Initialize config and env *)
  let config = Whyconf.init_config None in
  let main = Whyconf.get_main config in
  let env = Env.create_env (Whyconf.loadpath main) in

  let mods = build_mods env name expr in
  let tasks = extract_tasks mods in

  Log.debug "split %d tasks" (List.length tasks);
  List.iteri (fun i t ->
      let msg = Format.asprintf "@[<v 0>== Task %d ==@ \n%a@]@." (i + 1)
                  Why3.Pretty.print_task t
      in
      Log.debug "%s" msg
    ) tasks;

  let prover_name = "Coq" in
  let coq_filter = Whyconf.parse_filter_prover prover_name in
  let provers = Whyconf.filter_provers config coq_filter in
  if Whyconf.Mprover.is_empty provers then begin
      let all_provers = Whyconf.get_provers config in
      Whyconf.Mprover.keys all_provers
      |> fun ps -> prerr_endline (Printf.sprintf "prover length: %d" (List.length ps)); ps
      |>  List.iter (fun key -> prerr_endline key.Whyconf.prover_name);
      failwith (prover_name ^ " is not installed or configured.");
    end;

  let coq_config = snd (Whyconf.Mprover.max_binding provers) in
  let coq_driver = Driver.load_driver_for_prover main env coq_config in

  (* Print theorems of Coq *)
  Format.printf "(* --- Realizeing Task --- *)@\n";
  List.iter (fun task ->
      Driver.print_task coq_driver Format.std_formatter task) tasks


let _ = verify "dummy" [example5_fun; example5_spec]