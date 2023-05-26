(* {{{ COPYING *(

  This file is part of Merlin, an helper for ocaml editors

  Copyright (C) 2013 - 2015  Frédéric Bour  <frederic.bour(_)lakaban.net>
                             Thomas Refis  <refis.thomas(_)gmail.com>
                             Simon Castellan  <simon.castellan(_)iuwt.fr>

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
  sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  The Software is provided "as is", without warranty of any kind, express or
  implied, including but not limited to the warranties of merchantability,
  fitness for a particular purpose and noninfringement. In no event shall
  the authors or copyright holders be liable for any claim, damages or other
  liability, whether in an action of contract, tort or otherwise, arising
  from, out of or in connection with the software or the use or other dealings
  in the Software.

)* }}} *)

open Std
open Option.Infix

(* Réglisse la police *)
open Typedtree

open Browse_raw
open Browse_tree

let id_of_patt = function
  | { pat_desc = Tpat_var (id, _) ; _ } -> Some id
  | _ -> None

let mk ~is_public ?(children=[]) ~location ~deprecated outline_kind outline_type id =
  { Query_protocol. is_public; outline_kind; outline_type; location; children;
    outline_name = Ident.name id ; deprecated }

let get_class_field_desc_infos = function
  | Typedtree.Tcf_val (str_loc,_,_,_,_) -> Some (str_loc, `Value)
  | Typedtree.Tcf_method (str_loc,_,_)  -> Some (str_loc, `Method)
  | _ -> None

let outline_type ~env typ =
  let ppf, to_string = Format.to_string () in
  Printtyp.wrap_printing_env env (fun () ->
    Type_utils.print_type_with_decl ~verbosity:(Mconfig.Verbosity.Lvl 0) env ppf typ);
  Some (to_string ())

let rec summarize is_public_of_loc node =
  let location = node.t_loc in
  let is_public = is_public_of_loc location in
  let mk = mk ~is_public in
  match node.t_node with
  | Value_binding vb      ->
    let deprecated = Type_utils.is_deprecated vb.vb_attributes in
    begin match id_of_patt vb.vb_pat with
    | None -> None
    | Some ident ->
      let typ = outline_type ~env:node.t_env vb.vb_pat.pat_type in
      Some (mk ~location ~deprecated `Value typ ident)
    end
  | Value_description vd  ->
    let deprecated = Type_utils.is_deprecated vd.val_attributes in
    let typ = outline_type ~env:node.t_env vd.val_val.val_type in
    Some (mk ~location ~deprecated `Value typ vd.val_id)

  | Module_declaration md ->
    let children = get_mod_children is_public_of_loc node in
    begin match md.md_id with
    | None -> None
    | Some id ->
      let deprecated = Type_utils.is_deprecated md.md_attributes in
      Some (mk ~children ~location ~deprecated `Module None id)
    end

  | Module_binding mb ->
    let children = get_mod_children is_public_of_loc node in
    begin match mb.mb_id with
    | None -> None
    | Some id ->
      let deprecated = Type_utils.is_deprecated mb.mb_attributes in
      Some (mk ~children ~location ~deprecated `Module None id)
    end

  | Module_type_declaration mtd ->
    let children = get_mod_children is_public_of_loc node in
    let deprecated = Type_utils.is_deprecated mtd.mtd_attributes in
    Some (mk ~deprecated ~children ~location `Modtype None mtd.mtd_id)

  | Type_declaration td ->
    let children =
      List.concat_map (Lazy.force node.t_children) ~f:(fun child ->
        match child.t_node with
        | Type_kind _ ->
          List.map (Lazy.force child.t_children) ~f:(fun x ->
            match x.t_node with
            | Constructor_declaration c ->
              let deprecated = Type_utils.is_deprecated c.cd_attributes in
              mk `Constructor None c.cd_id ~deprecated ~location:c.cd_loc
            | Label_declaration ld ->
              let deprecated = Type_utils.is_deprecated ld.ld_attributes in
              mk `Label None ld.ld_id ~deprecated ~location:ld.ld_loc
            | _ -> assert false (* ! *)
          )
        | _ -> []
      )
    in
    let deprecated = Type_utils.is_deprecated td.typ_attributes in
    Some (mk ~children ~location ~deprecated `Type None td.typ_id)
  | Type_extension te ->
    let name = Path.name te.tyext_path in
    let children =
      List.filter_map (Lazy.force node.t_children) ~f:(fun x ->
        summarize is_public_of_loc x >>| fun x -> 
          { x with Query_protocol.outline_kind = `Constructor }
      )
    in
    let deprecated = Type_utils.is_deprecated te.tyext_attributes in
    Some { Query_protocol. is_public; outline_name = name; outline_kind = `Type
         ; outline_type = None; location; children; deprecated }

  | Extension_constructor ec ->
    let deprecated = Type_utils.is_deprecated ec.ext_attributes in
    Some (mk ~location `Exn None ec.ext_id ~deprecated)

  | Class_declaration cd ->
    let children =
      List.concat_map 
        (Lazy.force node.t_children) 
        ~f:(get_class_elements is_public_of_loc)
    in
    let deprecated = Type_utils.is_deprecated cd.ci_attributes in
    Some (mk ~children ~location `Class None cd.ci_id_class_type ~deprecated)

  | _ -> None

and get_class_elements is_public_of_loc node =
  let is_public = is_public_of_loc node.t_loc in
  match node.t_node with
  | Class_expr _ ->
    List.concat_map (Lazy.force node.t_children) ~f:(get_class_elements is_public_of_loc)
  | Class_structure _ ->
    List.filter_map (Lazy.force node.t_children) ~f:(fun child ->
      match child.t_node with
      | Class_field cf ->
        begin match get_class_field_desc_infos cf.cf_desc with
        | Some (str_loc, outline_kind) ->
          let deprecated = Type_utils.is_deprecated cf.cf_attributes in
          Some { Query_protocol.
            is_public;
            outline_name = str_loc.Location.txt;
            outline_kind;
            outline_type = None;
            location = str_loc.Location.loc;
            children = [];
            deprecated
          }
        | None -> None
        end
      | _ -> None
    )
  | _ -> []

and get_mod_children is_public_of_loc node =
  List.concat_map (Lazy.force node.t_children) ~f:(remove_mod_indir is_public_of_loc)

and remove_mod_indir is_public_of_loc node =
  match node.t_node with
  | Module_expr _
  | Module_type _ ->
    List.concat_map (Lazy.force node.t_children) ~f:(remove_mod_indir is_public_of_loc)
  | _ -> remove_top_indir is_public_of_loc node

and remove_top_indir is_public_of_loc t =
  match t.t_node with
  | Structure _
  | Signature _ -> 
      List.concat_map ~f:(remove_top_indir is_public_of_loc) (Lazy.force t.t_children)
  | Signature_item _
  | Structure_item _ -> 
      List.filter_map (Lazy.force t.t_children) ~f:(summarize is_public_of_loc)
  | _ -> []

let build_index ~end_pos ~config ~env ~local_defs dclsig = 
  let r =
  List.filter_map dclsig ~f:Types.(
    function 
    | Sig_value (ident, _, _) ->
        let name = Ident.name ident in
        let locate = 
          Locate.from_string
            ~config ~env ~local_defs ~pos:end_pos `ML name
        in
        ( match locate with
          | `Found (_, _file, pos) -> Some pos 
          | _ -> failwith "oupsi" ) 
    | _ -> None) 
  in
  Printf.eprintf "Built index of size %s\n%!" 
  (r |> List.map ~f:(Lexing.print_position ()) |> String.concat ~sep:"| ")   ;
  r
let is_public_of_loc ~end_pos ~config ~env ~local_defs ~sourcefile ~modulename = 
  let sourceintf =
    Filename.remove_extension sourcefile ^ !Config.interface_suffix
  in
  if not @@ Sys.file_exists sourceintf then (
    Printf.printf "%s mli not found\n%!" sourceintf;
    (fun _ -> false) )
  else begin
    let cmi_name = "merlin_analysis__" ^ modulename ^ ".cmi" in
    let modulename = "Merlin_analysis__" ^ modulename in
    try
      let intf_file = Load_path.find_uncap cmi_name in
      let dclsig = Env.read_signature modulename intf_file in
      let index = build_index ~end_pos ~config ~env ~local_defs dclsig in
      ( fun loc -> 
        List.exists 
          ~f:( fun pos ->
            let start = loc.Warnings.loc_start in
            let end_ = loc.Warnings.loc_end in
            Lexing.compare_pos start pos <= 0 && Lexing.compare_pos end_ pos >= 0 
          )
          index
      )
    with Not_found -> (
      Printf.printf "%s cmi not found\n%!" cmi_name ;
      (fun _ -> false) )
  end

let get ~pipeline browses = 
  let end_pos = Mpipeline.get_lexing_pos pipeline `End in
  let config = Mpipeline.final_config pipeline in
  let sourcefile = config.query.directory ^ "/" ^ config.query.filename in
  let typer = Mpipeline.typer_result pipeline in
  let env =
    match Mtyper.get_typedtree typer with
    | `Implementation structure -> structure.str_final_env
    | `Interface signature -> signature.sig_final_env
  in
  
  let modulename = Env.get_unit_name () in
  let local_defs = Mtyper.get_typedtree typer in
  let is_public_of_loc = 
    is_public_of_loc ~end_pos ~config ~env ~local_defs ~sourcefile ~modulename
  in
  List.concat @@ List.rev_map ~f:(remove_top_indir is_public_of_loc) browses

let shape cursor nodes =
  let rec aux node =
    (* A node is selected if:
       - part of the module language
       - or under the cursor *)
    let selected = match node.t_node with
      | Module_expr _
      | Module_type_constraint _
      | Structure _
      | Structure_item _
      | Module_binding _
      | Module_type _
      | Signature _
      | Signature_item _
      | Module_declaration _
      | Module_type_declaration _
      | Module_binding_name _
      | Module_declaration_name _
      | Module_type_declaration_name _ -> not node.t_loc.Location.loc_ghost
      | _ -> Location_aux.compare_pos cursor node.t_loc = 0 &&
             Lexing.compare_pos node.t_loc.Location.loc_start cursor <> 0 &&
             Lexing.compare_pos node.t_loc.Location.loc_end cursor <> 0
    in
    if selected then [{
        Query_protocol.
        shape_loc = node.t_loc;
        shape_sub = List.concat_map ~f:aux (Lazy.force node.t_children)
      }]
    else []
  in
  List.concat_map ~f:aux nodes
