 
structure LCTR_Native_Metadata =
struct
  fun emit thy names =
    let
      val axioms = Symtab.make (map (fn (n, _) => (n, ())) (Theory.all_axioms_of thy));
      val cache = Unsynchronized.ref (Inttab.empty: unit Symtab.table Inttab.table);
      fun axname n acc = if Symtab.defined axioms n then Symtab.update (n, ()) acc else acc;
      fun atom (Proofterm.PAxm (n, _, _)) = Symtab.update (n, ())
        | atom _ = I;
      fun body_axioms (Proofterm.PBody {thms, proof, ...}) =
        let
          val direct = Proofterm.fold_proof_atoms false atom [proof] Symtab.empty;
        in fold (fn node => Symtab.merge (K true) o pair (node_axioms node)) thms direct end
      and node_axioms (i, node) =
        (case Inttab.lookup (!cache) i of
          SOME result => result
        | NONE => let
            val result = body_axioms (Future.join (Proofterm.thm_node_body node))
              |> axname (#1 (Proofterm.thm_node_name node));
            val _ = cache := Inttab.update (i, result) (!cache);
          in result end);
      fun strings xs = "[" ^ commas (map quote xs) ^ "]";
      fun field (name, value) = quote name ^ ":" ^ value;
      fun record name =
        let
          val (base, index) = Thm_Name.parse name;
          val facts = Global_Theory.get_thms thy base;
          val thms = if index = 0 then facts else [nth facts (index - 1)];
          val ax = fold (fn th => Symtab.merge (K true) o pair (body_axioms (Thm.proof_body_of th))) thms Symtab.empty;
          val deps = Thm_Deps.thm_deps thy thms |> map (#2 #> Thm_Name.print) |> sort_distinct string_ord;
          val oracles = Thm_Deps.all_oracles thms |> map (#1 #> #1) |> sort_distinct string_ord;
          val _ = if member (op =) oracles "Pure.skip_proof" then error "Unproved fact" else ();
        in "{" ^ commas (map field [("name", quote name), ("fact_instances", string_of_int (length thms)),
          ("axiomatic_dependencies", strings (Symtab.keys ax)), ("theorem_dependencies", strings deps),
          ("oracle_dependencies", strings oracles)]) ^ "}" end;
      val json = "{\"records\":[" ^ commas (map record names) ^ "]}";
    in Export.export thy (Path.binding0 (Path.explode "lctr-metadata/facts.json")) [XML.Text json] end;
end;
