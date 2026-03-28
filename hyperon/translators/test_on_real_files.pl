%% Test HE ↔ PeTTa translators on real .metta files
%%
%% Uses metta_parser.pl for correct parsing of ALL MeTTa syntax.
%% Uses he_to_petta.pl / petta_to_he.pl for translation.
%%
%% Usage:
%%   swipl -l test_on_real_files.pl -g batch_test_he_to_petta -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file('input.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_he_to_petta('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_he_to_petta_trusted('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_he_to_petta_recursive('in.metta','.he2petta.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_he_to_petta_bundle('in.metta','bundle_dir')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_trusted('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_raw('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_extended('in.metta','out.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_mode('in.metta','out.metta',extended)" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_recursive('in.metta','.petta2he.metta')" -g halt
%%   swipl -l test_on_real_files.pl -g "translate_file_petta_to_he_bundle('in.metta','bundle_dir')" -g halt

:- use_module(metta_parser).
:- use_module(library(filesex),
              [ make_directory_path/1,
                copy_file/2,
                delete_directory_and_contents/1
              ]).
:- use_module(he_to_petta, [translate_term/2 as he_translate_term,
                             translate_term_trusted/2 as he_translate_term_trusted,
                             translate_decl/2 as he_translate_decl,
                             translate_decl_trusted/2 as he_translate_decl_trusted,
                             obsolete_bool_and_rule/1,
                             should_drop_obsolete_bool_and_rule/1]).
:- use_module(petta_to_he, [translate_term/2 as pe_translate_term,
                             translate_term_extended/2 as pe_translate_term_ext,
                             translate_term_trusted/2 as pe_translate_term_trusted,
                             translate_decl/2 as pe_translate_decl,
                             translate_decl_extended/2 as pe_translate_decl_ext,
                             translate_decl_trusted/2 as pe_translate_decl_trusted,
                             optimize_term/2 as pe_optimize_term,
                             optimize_decl/2 as pe_optimize_decl]).

%% ── File-level translation ──────────────────────────────────────
%%
%% Local module compatibility layer:
%% When a file is translated into a different output directory, plain local
%% `.metta` import paths and `register-module!` roots must be relocated
%% relative to the translated output file. This is intentionally scoped to
%% resolvable local filesystem modules. Host stdlib modules, git providers,
%% Python-backed imports, and other runtime-provided surfaces are left
%% untouched by design.

translate_file(Path) :-
    read_metta_file(Path, Atoms),
    length(Atoms, N),
    format("; Translated from HE to PeTTa (~w atoms)~n", [N]),
    format("; Source: ~w~n~n", [Path]),
    translate_toplevel_atoms(he_to_petta, Atoms, TAtoms),
    forall(member(TA, TAtoms), write_toplevel_atom(current_output, TA)).

translate_file_he_to_petta(InPath, OutPath) :-
    translate_file_to_path(he_to_petta, InPath, OutPath).

translate_file_he_to_petta_trusted(InPath, OutPath) :-
    translate_file_to_path(he_to_petta_trusted, InPath, OutPath).

translate_file_he_to_petta_recursive(InPath, OutSuffix) :-
    translate_file_tree_inplace(he_to_petta, InPath, OutSuffix).

translate_file_he_to_petta_bundle(InPath, BundleDir) :-
    translate_file_tree_to_dir(he_to_petta, InPath, BundleDir, bundle).

translate_file_petta_to_he(InPath, OutPath) :-
    translate_file_to_path(petta_to_he, InPath, OutPath).

translate_file_petta_to_he_trusted(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_trusted, InPath, OutPath).

translate_file_petta_to_he_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_raw, InPath, OutPath).

translate_file_petta_to_he_extended(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_extended, InPath, OutPath).

translate_file_petta_to_he_extended_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_extended_raw, InPath, OutPath).

translate_file_petta_to_he_recursive(InPath, OutSuffix) :-
    translate_file_tree_inplace(petta_to_he, InPath, OutSuffix).

translate_file_petta_to_he_bundle(InPath, BundleDir) :-
    translate_file_tree_to_dir(petta_to_he, InPath, BundleDir, bundle).

translate_file_he_to_petta_mode(InPath, OutPath, pure) :-
    translate_file_he_to_petta(InPath, OutPath).
translate_file_he_to_petta_mode(InPath, OutPath, trusted) :-
    translate_file_he_to_petta_trusted(InPath, OutPath).

translate_file_petta_to_he_mode(InPath, OutPath, pure) :-
    translate_file_petta_to_he(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, trusted) :-
    translate_file_petta_to_he_trusted(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended) :-
    translate_file_petta_to_he_extended(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, raw) :-
    translate_file_petta_to_he_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended_raw) :-
    translate_file_petta_to_he_extended_raw(InPath, OutPath).

translate_file_to_path(Direction, InPath, OutPath) :-
    absolute_file_name(InPath, AbsInPath, [relative_to('.'), solutions(first)]),
    absolute_file_name(OutPath, AbsOutPath, [relative_to('.'), solutions(first)]),
    file_directory_name(AbsOutPath, OutDir),
    make_directory_path(OutDir),
    read_metta_file(AbsInPath, Atoms),
    length(Atoms, N),
    setup_call_cleanup(
        open(AbsOutPath, write, Stream),
        (
            write_translation_header(Stream, Direction, AbsInPath, N),
            translate_toplevel_atoms(Direction, Atoms, TAtoms),
            relocate_local_module_surfaces(AbsInPath, AbsOutPath, TAtoms, CompatAtoms),
            forall(member(TA, CompatAtoms), write_toplevel_atom(Stream, TA))
        ),
        close(Stream)
    ).

translate_file_tree_to_dir(Direction, InPath, OutDir, TreeMode) :-
    absolute_file_name(InPath, AbsInPath, [relative_to('.'), solutions(first)]),
    absolute_file_name(OutDir, AbsOutDir, [relative_to('.'), solutions(first)]),
    make_directory_path(AbsOutDir),
    file_directory_name(AbsInPath, SourceRootDir),
    translate_file_tree_recursive(Direction, TreeMode, SourceRootDir, AbsOutDir,
        AbsInPath, [], SeenPairs),
    (   TreeMode == bundle
    ->  write_bundle_manifest(Direction, AbsInPath, AbsOutDir, SeenPairs)
    ;   true
    ).

translate_file_tree_inplace(Direction, InPath, OutSuffix) :-
    absolute_file_name(InPath, AbsInPath, [relative_to('.'), solutions(first)]),
    translate_file_tree_inplace_recursive(Direction, AbsInPath, OutSuffix, [], _).

write_translation_header(Stream, he_to_petta, InPath, N) :-
    format(Stream, "; Translated from HE to PeTTa (~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, he_to_petta_trusted, InPath, N) :-
    format(Stream, "; Translated from HE to PeTTa (trusted, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, petta_to_he, InPath, N) :-
    format(Stream, "; Translated from PeTTa to HE (~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, petta_to_he_trusted, InPath, N) :-
    format(Stream, "; Translated from PeTTa to HE (trusted, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, petta_to_he_raw, InPath, N) :-
    format(Stream, "; Translated from PeTTa to HE (raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, petta_to_he_extended, InPath, N) :-
    format(Stream, "; Translated from PeTTa to HE (extended, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).
write_translation_header(Stream, petta_to_he_extended_raw, InPath, N) :-
    format(Stream, "; Translated from PeTTa to HE (extended raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [InPath]).

translate_decl_for(he_to_petta, A, TA) :-
    safe_translate_he(A, TA).
translate_decl_for(he_to_petta_trusted, A, TA) :-
    safe_translate_he_trusted(A, TA).
translate_decl_for(petta_to_he, A, TA) :-
    safe_translate_pe(A, TA).
translate_decl_for(petta_to_he_trusted, A, TA) :-
    safe_translate_pe_trusted(A, TA).
translate_decl_for(petta_to_he_raw, A, TA) :-
    safe_translate_pe_raw(A, TA).
translate_decl_for(petta_to_he_extended, A, TA) :-
    safe_translate_pe_extended(A, TA).
translate_decl_for(petta_to_he_extended_raw, A, TA) :-
    safe_translate_pe_extended_raw(A, TA).

translate_term_for(he_to_petta, A, TA) :-
    he_translate_term(A, TA).
translate_term_for(he_to_petta_trusted, A, TA) :-
    he_translate_term_trusted(A, TA).
translate_term_for(petta_to_he, A, TA) :-
    pe_translate_term(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_trusted, A, TA) :-
    pe_translate_term_trusted(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_raw, A, TA) :-
    pe_translate_term(A, TA).
translate_term_for(petta_to_he_extended, A, TA) :-
    pe_translate_term_ext(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_extended_raw, A, TA) :-
    pe_translate_term_ext(A, TA).

translate_toplevel_atoms(Direction, Atoms, TAtoms) :-
    translate_toplevel_atoms_acc(Direction, Atoms, TAtoms0),
    postprocess_toplevel_atoms(Direction, Atoms, TAtoms0, TAtoms).

translate_toplevel_atoms_acc(_, [], []).
translate_toplevel_atoms_acc(Direction, ['!' , Expr | Rest], [exec(TExpr) | TRest]) :-
    translate_term_for(Direction, Expr, TExpr),
    translate_toplevel_atoms_acc(Direction, Rest, TRest).
translate_toplevel_atoms_acc(Direction, [A | Rest], [plain(TA) | TRest]) :-
    translate_toplevel_atom(Direction, A, TA),
    translate_toplevel_atoms_acc(Direction, Rest, TRest).

translate_toplevel_atom(Direction, A, TA) :-
    (   A = ['=', _, _]
    ;   A = [':', _, _]
    ),
    !,
    translate_decl_for(Direction, A, TA).
translate_toplevel_atom(Direction, A, TA) :-
    translate_term_for(Direction, A, TA).

postprocess_toplevel_atoms(he_to_petta, Atoms, TAtoms0, TAtoms) :-
    (   should_drop_obsolete_bool_and_rule(Atoms)
    ->  exclude(is_obsolete_bool_and_item, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).
postprocess_toplevel_atoms(he_to_petta_trusted, Atoms, TAtoms0, TAtoms) :-
    postprocess_toplevel_atoms(he_to_petta, Atoms, TAtoms0, TAtoms).
postprocess_toplevel_atoms(_, _, TAtoms, TAtoms).

is_obsolete_bool_and_item(plain(Expr)) :-
    obsolete_bool_and_rule(Expr).
is_obsolete_bool_and_item(_) :-
    fail.

%% ── Local module/path compatibility for translated files ────────

relocate_local_module_surfaces(SourcePath, OutputPath, TAtoms, CompatAtoms) :-
    maplist(relocate_toplevel_atom(SourcePath, OutputPath), TAtoms, CompatAtoms).

relocate_toplevel_atom(SourcePath, OutputPath, exec(Expr), exec(TExpr)) :-
    relocate_module_term(SourcePath, OutputPath, Expr, TExpr).
relocate_toplevel_atom(SourcePath, OutputPath, plain(Expr), plain(TExpr)) :-
    relocate_module_term(SourcePath, OutputPath, Expr, TExpr).

relocate_module_term(SourcePath, OutputPath, ['import!', Space, Spec],
                     ['import!', TSpace, TSpec]) :-
    relocate_module_term(SourcePath, OutputPath, Space, TSpace),
    relocate_local_import_spec(SourcePath, OutputPath, Spec, TSpec), !.
relocate_module_term(SourcePath, OutputPath, [include, Spec], [include, TSpec]) :-
    relocate_local_import_spec(SourcePath, OutputPath, Spec, TSpec), !.
relocate_module_term(SourcePath, OutputPath, ['register-module!', Root],
                     ['register-module!', TRoot]) :-
    relocate_local_module_root(SourcePath, OutputPath, Root, TRoot), !.
relocate_module_term(SourcePath, OutputPath, List, TList) :-
    is_list(List),
    maplist(relocate_module_term(SourcePath, OutputPath), List, TList), !.
relocate_module_term(_, _, X, X) :-
    \+ is_list(X).

relocate_local_import_spec(SourcePath, OutputPath, Spec, TSpec) :-
    (   resolve_local_module_file(SourcePath, Spec, Resolved, Style)
    ->  relativize_spec_for_output(OutputPath, Resolved, Style, TSpec)
    ;   TSpec = Spec
    ).

relocate_local_module_root(SourcePath, OutputPath, Root, TRoot) :-
    (   resolve_local_module_dir(SourcePath, Root, Resolved, Style)
    ->  relativize_spec_for_output(OutputPath, Resolved, Style, TRoot)
    ;   TRoot = Root
    ).

resolve_local_module_file(SourcePath, Spec, Resolved, Style) :-
    spec_payload(Spec, Payload, Style),
    file_directory_name(SourcePath, SourceDir),
    module_file_candidate(Payload, Candidate),
    absolute_file_name(Candidate, Resolved0, [relative_to(SourceDir), solutions(first)]),
    exists_file(Resolved0),
    atom_concat(_, '.metta', Resolved0),
    Resolved = Resolved0, !.

resolve_local_module_dir(SourcePath, Spec, Resolved, Style) :-
    spec_payload(Spec, Payload, Style),
    file_directory_name(SourcePath, SourceDir),
    absolute_file_name(Payload, Resolved0, [relative_to(SourceDir), solutions(first)]),
    exists_directory(Resolved0),
    Resolved = Resolved0, !.

module_file_candidate(Payload, Payload) :-
    atom_concat(_, '.metta', Payload).
module_file_candidate(Payload, Payload) :-
    \+ atom_concat(_, '.metta', Payload).
module_file_candidate(Payload, Candidate) :-
    \+ atom_concat(_, '.metta', Payload),
    atom_concat(Payload, '.metta', Candidate).

spec_payload(Spec, Payload, quoted) :-
    atom(Spec),
    atom_chars(Spec, ['"'|Rest]),
    append(Mid, ['"'], Rest),
    atom_chars(Payload, Mid), !.
spec_payload(Spec, Spec, bare) :-
    atom(Spec).

relativize_spec_for_output(OutputPath, Resolved, Style, TSpec) :-
    file_directory_name(OutputPath, OutputDir),
    relative_file_name(Resolved, OutputDir, Rel),
    rebuild_spec(Rel, Style, TSpec).

rebuild_spec(Payload, bare, Payload).
rebuild_spec(Payload, quoted, Spec) :-
    atomic_list_concat(['"', Payload, '"'], Spec).

translate_file_tree_inplace_recursive(_, SourcePath, _, Seen, Seen) :-
    memberchk(pair(SourcePath, _), Seen), !.
translate_file_tree_inplace_recursive(Direction, SourcePath, OutSuffix,
                                      SeenIn, SeenOut) :-
    translated_sibling_path(SourcePath, OutSuffix, OutPath),
    read_metta_file(SourcePath, Atoms),
    length(Atoms, N),
    translate_toplevel_atoms(Direction, Atoms, TAtoms0),
    rewrite_inplace_recursive_module_surfaces(SourcePath, OutPath, OutSuffix,
        TAtoms0, TAtoms, Deps),
    setup_call_cleanup(
        open(OutPath, write, Stream),
        (
            write_translation_header(Stream, Direction, SourcePath, N),
            format(Stream, "; Mode: recursive~n~n", []),
            forall(member(TA, TAtoms), write_toplevel_atom(Stream, TA))
        ),
        close(Stream)
    ),
    SeenMid = [pair(SourcePath, OutPath)|SeenIn],
    translate_inplace_deps_recursive(Direction, OutSuffix, Deps, SeenMid, SeenOut).

translate_inplace_deps_recursive(_, _, [], Seen, Seen).
translate_inplace_deps_recursive(Direction, OutSuffix, [Dep|Deps], SeenIn, SeenOut) :-
    translate_file_tree_inplace_recursive(Direction, Dep, OutSuffix, SeenIn, SeenMid),
    translate_inplace_deps_recursive(Direction, OutSuffix, Deps, SeenMid, SeenOut).

translated_sibling_path(SourcePath, OutSuffix, OutPath) :-
    file_directory_name(SourcePath, Dir),
    file_base_name(SourcePath, BaseName),
    atom_concat(Stem, '.metta', BaseName),
    atom_concat(Stem, OutSuffix, OutBase),
    directory_file_path(Dir, OutBase, OutPath).

rewrite_inplace_recursive_module_surfaces(SourcePath, OutPath, OutSuffix,
                                          TAtoms0, TAtoms, Deps) :-
    rewrite_inplace_recursive_module_surfaces_acc(SourcePath, OutPath, OutSuffix,
        TAtoms0, [], TAtoms, [], DepPairs),
    sort(DepPairs, Deps).

rewrite_inplace_recursive_module_surfaces_acc(_, _, _, [], _, [], DepAcc, DepAcc).
rewrite_inplace_recursive_module_surfaces_acc(SourcePath, OutPath, OutSuffix,
                                              [Atom|Atoms], EnvIn, [TAtom|TAtoms],
                                              DepIn, DepOut) :-
    rewrite_inplace_recursive_toplevel_atom(SourcePath, OutPath, OutSuffix,
        Atom, EnvIn, TAtom, EnvMid, AtomDeps),
    append(DepIn, AtomDeps, DepMid),
    rewrite_inplace_recursive_module_surfaces_acc(SourcePath, OutPath, OutSuffix,
        Atoms, EnvMid, TAtoms, DepMid, DepOut).

rewrite_inplace_recursive_toplevel_atom(SourcePath, _OutPath, _OutSuffix,
                                        exec(['register-module!', Root]),
                                        EnvIn, exec(['register-module!', Root]), EnvOut, []) :-
    (   resolve_local_module_dir(SourcePath, Root, ResolvedDir, _Style)
    ->  module_root_name(ResolvedDir, RootName),
        update_module_root_env(RootName, ResolvedDir, EnvIn, EnvOut)
    ;   EnvOut = EnvIn
    ), !.
rewrite_inplace_recursive_toplevel_atom(SourcePath, OutPath, OutSuffix,
                                        exec(['import!', Space, Spec]),
                                        EnvIn, exec(['import!', Space, TSpec]), EnvIn, Deps) :-
    (   resolve_recursive_import(SourcePath, EnvIn, Spec, ResolvedFile, Style)
    ->  translated_sibling_path(ResolvedFile, OutSuffix, TargetFile),
        relativize_spec_for_output(OutPath, TargetFile, Style, TSpec),
        Deps = [ResolvedFile]
    ;   TSpec = Spec,
        Deps = []
    ), !.
rewrite_inplace_recursive_toplevel_atom(SourcePath, OutPath, OutSuffix,
                                        exec([include, Spec]),
                                        EnvIn, exec([include, TSpec]), EnvIn, Deps) :-
    (   resolve_recursive_import(SourcePath, EnvIn, Spec, ResolvedFile, Style)
    ->  translated_sibling_path(ResolvedFile, OutSuffix, TargetFile),
        relativize_spec_for_output(OutPath, TargetFile, Style, TSpec),
        Deps = [ResolvedFile]
    ;   TSpec = Spec,
        Deps = []
    ), !.
rewrite_inplace_recursive_toplevel_atom(_, _, _, Atom, Env, Atom, Env, []).

translate_file_tree_recursive(_, _, _, _, SourcePath, Seen, Seen) :-
    memberchk(pair(SourcePath, _), Seen), !.
translate_file_tree_recursive(Direction, TreeMode, SourceRootDir, OutputRootDir,
                              SourcePath, SeenIn, SeenOut) :-
    output_path_for_source(SourceRootDir, OutputRootDir, SourcePath, OutPath),
    read_metta_file(SourcePath, Atoms),
    length(Atoms, N),
    translate_toplevel_atoms(Direction, Atoms, TAtoms0),
    rewrite_recursive_module_surfaces(SourceRootDir, OutputRootDir, SourcePath,
        OutPath, TAtoms0, TAtoms, Deps),
    file_directory_name(OutPath, OutFileDir),
    make_directory_path(OutFileDir),
    setup_call_cleanup(
        open(OutPath, write, Stream),
        (
            write_translation_header(Stream, Direction, SourcePath, N),
            (   TreeMode == bundle
            ->  format(Stream, "; Mode: bundle~n~n", [])
            ;   TreeMode == recursive
            ->  format(Stream, "; Mode: recursive~n~n", [])
            ;   true
            ),
            forall(member(TA, TAtoms), write_toplevel_atom(Stream, TA))
        ),
        close(Stream)
    ),
    SeenMid = [pair(SourcePath, OutPath)|SeenIn],
    translate_deps_recursive(Direction, TreeMode, SourceRootDir, OutputRootDir,
        Deps, SeenMid, SeenOut).

translate_deps_recursive(_, _, _, _, [], Seen, Seen).
translate_deps_recursive(Direction, TreeMode, SourceRootDir, OutputRootDir,
                         [Dep|Deps], SeenIn, SeenOut) :-
    translate_file_tree_recursive(Direction, TreeMode, SourceRootDir, OutputRootDir,
        Dep, SeenIn, SeenMid),
    translate_deps_recursive(Direction, TreeMode, SourceRootDir, OutputRootDir,
        Deps, SeenMid, SeenOut).

output_path_for_source(SourceRootDir, OutputRootDir, SourcePath, OutPath) :-
    relative_file_name(SourcePath, SourceRootDir, RelPath),
    directory_file_path(OutputRootDir, RelPath, OutPath).

output_path_for_source_dir(SourceRootDir, OutputRootDir, SourceDir, OutDir) :-
    relative_file_name(SourceDir, SourceRootDir, RelDir),
    directory_file_path(OutputRootDir, RelDir, OutDir).

rewrite_recursive_module_surfaces(SourceRootDir, OutputRootDir, SourcePath,
                                  OutPath, TAtoms0, TAtoms, Deps) :-
    rewrite_recursive_module_surfaces_acc(SourceRootDir, OutputRootDir, SourcePath,
        OutPath, TAtoms0, [], TAtoms, [], DepPairs),
    sort(DepPairs, Deps).

rewrite_recursive_module_surfaces_acc(_, _, _, _, [], _, [], DepAcc, DepAcc).
rewrite_recursive_module_surfaces_acc(SourceRootDir, OutputRootDir, SourcePath,
                                      OutPath, [Atom|Atoms], EnvIn, [TAtom|TAtoms],
                                      DepIn, DepOut) :-
    rewrite_recursive_toplevel_atom(SourceRootDir, OutputRootDir, SourcePath,
        OutPath, Atom, EnvIn, TAtom, EnvMid, AtomDeps),
    append(DepIn, AtomDeps, DepMid),
    rewrite_recursive_module_surfaces_acc(SourceRootDir, OutputRootDir, SourcePath,
        OutPath, Atoms, EnvMid, TAtoms, DepMid, DepOut).

rewrite_recursive_toplevel_atom(SourceRootDir, OutputRootDir, SourcePath, OutPath,
                                exec(['register-module!', Root]),
                                EnvIn, exec(['register-module!', TRoot]), EnvOut, []) :-
    (   resolve_local_module_dir(SourcePath, Root, ResolvedDir, Style)
    ->  output_path_for_source_dir(SourceRootDir, OutputRootDir, ResolvedDir, TargetDir),
        relativize_spec_for_output(OutPath, TargetDir, Style, TRoot),
        module_root_name(ResolvedDir, RootName),
        update_module_root_env(RootName, ResolvedDir, EnvIn, EnvOut)
    ;   TRoot = Root,
        EnvOut = EnvIn
    ), !.
rewrite_recursive_toplevel_atom(SourceRootDir, OutputRootDir, SourcePath, OutPath,
                                exec(['import!', Space, Spec]),
                                EnvIn, exec(['import!', Space, TSpec]), EnvIn, Deps) :-
    (   resolve_recursive_import(SourcePath, EnvIn, Spec, ResolvedFile, Style)
    ->  output_path_for_source(SourceRootDir, OutputRootDir, ResolvedFile, TargetFile),
        relativize_spec_for_output(OutPath, TargetFile, Style, TSpec),
        Deps = [ResolvedFile]
    ;   TSpec = Spec,
        Deps = []
    ), !.
rewrite_recursive_toplevel_atom(SourceRootDir, OutputRootDir, SourcePath, OutPath,
                                exec([include, Spec]),
                                EnvIn, exec([include, TSpec]), EnvIn, Deps) :-
    (   resolve_recursive_import(SourcePath, EnvIn, Spec, ResolvedFile, Style)
    ->  output_path_for_source(SourceRootDir, OutputRootDir, ResolvedFile, TargetFile),
        relativize_spec_for_output(OutPath, TargetFile, Style, TSpec),
        Deps = [ResolvedFile]
    ;   TSpec = Spec,
        Deps = []
    ), !.
rewrite_recursive_toplevel_atom(_, _, _, _, Atom, Env, Atom, Env, []).

resolve_recursive_import(SourcePath, _Env, Spec, ResolvedFile, Style) :-
    resolve_local_module_file(SourcePath, Spec, ResolvedFile, Style), !.
resolve_recursive_import(_, RootEnv, Spec, ResolvedFile, Style) :-
    resolve_registered_module_file(RootEnv, Spec, ResolvedFile, Style).

resolve_registered_module_file(Env, Spec, ResolvedFile, Style) :-
    spec_payload(Spec, Payload, Style),
    atomic_list_concat([RootName|Segments], ':', Payload),
    Segments \= [],
    memberchk(root(RootName, RootDir), Env),
    append(Prefix, [Leaf], Segments),
    directory_file_path_segments(RootDir, Prefix, StemDir),
    module_file_candidate(Leaf, LeafCandidate),
    directory_file_path(StemDir, LeafCandidate, Resolved0),
    exists_file(Resolved0),
    ResolvedFile = Resolved0.

directory_file_path_segments(Base, [], Base).
directory_file_path_segments(Base, [Seg|Segs], Out) :-
    directory_file_path(Base, Seg, Next),
    directory_file_path_segments(Next, Segs, Out).

module_root_name(ResolvedDir, RootName) :-
    file_base_name(ResolvedDir, RootName).

update_module_root_env(RootName, ResolvedDir, EnvIn,
                       [root(RootName, ResolvedDir)|EnvRest]) :-
    exclude(same_module_root(RootName), EnvIn, EnvRest).

same_module_root(RootName, root(RootName, _)).
same_module_root(RootName, root(Other, _)) :-
    RootName \== Other.

write_bundle_manifest(Direction, EntrySource, BundleDir, SeenPairs) :-
    directory_file_path(BundleDir, 'bundle_manifest.tsv', ManifestPath),
    output_path_for_source_from_entry(EntrySource, BundleDir, EntryOutput),
    setup_call_cleanup(
        open(ManifestPath, write, Stream),
        (
            format(Stream, "direction\tsource\toutput\tkind~n", []),
            format(Stream, "~w\t~w\t~w\tentry~n", [Direction, EntrySource, EntryOutput]),
            forall(member(pair(Source, Output), SeenPairs),
                (   Source == EntrySource
                ->  true
                ;   format(Stream, "~w\t~w\t~w\tdependency~n",
                          [Direction, Source, Output])
                ))
        ),
        close(Stream)
    ).

output_path_for_source_from_entry(EntrySource, BundleDir, EntryOutput) :-
    file_directory_name(EntrySource, SourceRootDir),
    output_path_for_source(SourceRootDir, BundleDir, EntrySource, EntryOutput).

%% Focused self-tests for the local module compatibility layer.
%% These are intentionally separate from the core term tests because they are
%% source/output-path aware and therefore belong to the file translator.

run_path_compat_tests :-
    format("~n=== File Translation Path Compatibility Tests ===~n"),
    forall(path_compat_case(N, Name, Goal), run_path_compat_case(N, Name, Goal)).

run_path_compat_case(N, Name, Goal) :-
    (   call(Goal)
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n", [N, Name]),
        fail
    ).

path_compat_case(1, "plain local import spec rewrites relative to translated output",
    relocate_local_import_spec(
        '/home/zar/claude/c-projects/cetta/tests/test_import_nested_depth.metta',
        '/home/zar/claude/hyperon/translators/.generated_path_compat/out/test_import_nested_depth.petta.metta',
        'support/import_deep/root.metta',
        '../../../c-projects/cetta/tests/support/import_deep/root.metta')).

path_compat_case(2, "bare helper import resolves to local .metta file",
    relocate_local_import_spec(
        '/home/zar/claude/c-projects/cetta/tests/support/import_pkg/moduleA.metta',
        '/home/zar/claude/hyperon/translators/.generated_path_compat/out/moduleA.he.metta',
        'Helper',
        '../../../c-projects/cetta/tests/support/import_pkg/Helper.metta')).

path_compat_case(3, "register-module! root relocates relative to translated output",
    relocate_local_module_root(
        '/home/zar/claude/c-projects/cetta/tests/test_import_modules.metta',
        '/home/zar/claude/hyperon/translators/.generated_path_compat/out/test_import_modules.petta.metta',
        'support/import_pkg',
        '../../../c-projects/cetta/tests/support/import_pkg')).

path_compat_case(4, "foreign/python import surface is intentionally untouched",
    relocate_local_import_spec(
        '/home/zar/claude/c-projects/cetta/tests/test_import_foreign_python_file.metta',
        '/home/zar/claude/hyperon/translators/.generated_path_compat/out/test_import_foreign_python_file.he.metta',
        'support/import_foreign_pyfile',
        'support/import_foreign_pyfile')).

path_compat_case(5, "recursive translation keeps files in place with renamed outputs",
    (   FixtureRoot = '/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture',
        setup_recursive_fixture(FixtureRoot),
        translate_file_he_to_petta_recursive(
            '/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture/test_import_modules.metta',
            '.he2petta.metta'),
        file_contains_text('/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture/test_import_modules.he2petta.metta',
            "!(register-module! support/import_pkg)"),
        file_contains_text('/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture/test_import_modules.he2petta.metta',
            "!(import! &db support/import_pkg/moduleA.he2petta.metta)"),
        exists_file('/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture/support/import_pkg/moduleA.he2petta.metta'),
        file_contains_text('/home/zar/claude/hyperon/translators/.generated_path_compat/inplace_fixture/support/import_pkg/moduleA.he2petta.metta',
            "!(import! &self Helper.he2petta.metta)")
    )).

path_compat_case(6, "bundle translation emits manifest and bundled entry file",
    (   BundleDir = '/home/zar/claude/hyperon/translators/.generated_path_compat/bundle_he',
        translate_file_he_to_petta_bundle(
            '/home/zar/claude/c-projects/cetta/tests/test_import_nested_depth.metta',
            BundleDir),
        exists_file('/home/zar/claude/hyperon/translators/.generated_path_compat/bundle_he/bundle_manifest.tsv'),
        file_contains_text('/home/zar/claude/hyperon/translators/.generated_path_compat/bundle_he/test_import_nested_depth.metta',
            "!(import! &deep support/import_deep/root.metta)"),
        exists_file('/home/zar/claude/hyperon/translators/.generated_path_compat/bundle_he/support/import_deep/root.metta')
    )).

file_contains_text(Path, Snippet) :-
    read_file_to_string(Path, Text, []),
    sub_string(Text, _, _, _, Snippet).

setup_recursive_fixture(FixtureRoot) :-
    (   exists_directory(FixtureRoot)
    ->  delete_directory_and_contents(FixtureRoot)
    ;   true
    ),
    make_directory_path(FixtureRoot),
    copy_fixture_relative(FixtureRoot, 'test_import_modules.metta'),
    copy_fixture_relative(FixtureRoot, 'support/import_pkg/moduleA.metta'),
    copy_fixture_relative(FixtureRoot, 'support/import_pkg/Helper.metta'),
    copy_fixture_relative(FixtureRoot, 'support/import_pkg/data/Facts.metta').

copy_fixture_relative(FixtureRoot, RelPath) :-
    directory_file_path('/home/zar/claude/c-projects/cetta/tests', RelPath, Source),
    directory_file_path(FixtureRoot, RelPath, Dest),
    file_directory_name(Dest, DestDir),
    make_directory_path(DestDir),
    copy_file(Source, Dest).

write_toplevel_atom(Stream, exec(Expr)) :-
    write(Stream, '!'),
    print_sexpr(Stream, Expr),
    nl(Stream).
write_toplevel_atom(Stream, plain(Expr)) :-
    print_sexpr(Stream, Expr),
    nl(Stream).

%% ── Batch test: all CeTTa HE test files ─────────────────────────

batch_test_he_to_petta :-
    CettaTests = '../../c-projects/cetta/tests/',
    format("=== Batch HE → PeTTa translation test ===~n~n"),
    directory_files(CettaTests, Files),
    include(is_metta_test, Files, TestFiles),
    sort(TestFiles, Sorted),
    length(Sorted, N),
    format("Found ~w test files~n~n", [N]),
    batch_process(CettaTests, Sorted, 0, 0).

is_metta_test(F) :-
    atom_concat(_, '.metta', F),
    (atom_concat('test_', _, F) ; atom_concat('he_', _, F)).

batch_process(_, [], Pass, Fail) :-
    Total is Pass + Fail,
    format("~n=== Results: ~w/~w parsed+translated, ~w failures ===~n",
           [Pass, Total, Fail]).
batch_process(Dir, [F|Fs], Pass, Fail) :-
    atom_concat(Dir, F, Path),
    (   catch(
            (   read_metta_file(Path, Atoms),
                length(Atoms, NA),
                maplist(safe_translate_he, Atoms, _),
                format("  ✓ ~w (~w atoms)~n", [F, NA]),
                P1 is Pass + 1, F1 = Fail
            ),
            Error,
            (   format("  ✗ ~w (~w)~n", [F, Error]),
                P1 = Pass, F1 is Fail + 1
            ))
    ),
    batch_process(Dir, Fs, P1, F1).

safe_translate_he(A, TA) :-
    (   A = ['=', _, _] -> he_translate_decl(A, TA)
    ;   A = [':', _, _] -> he_translate_decl(A, TA)
    ;   TA = A
    ).

safe_translate_he_trusted(A, TA) :-
    (   A = ['=', _, _] -> he_translate_decl_trusted(A, TA)
    ;   A = [':', _, _] -> he_translate_decl_trusted(A, TA)
    ;   he_translate_term_trusted(A, TA)
    ).

safe_translate_pe(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_trusted(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_trusted(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_trusted(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_trusted(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl(A, TA)
    ;   pe_translate_term(A, TA)
    ).

safe_translate_pe_extended(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_ext(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_ext(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_ext(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_extended_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_ext(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_ext(A, TA)
    ;   pe_translate_term_ext(A, TA)
    ).

%% ── Batch test: PeTTa → HE on PeTTa examples + miner ────────────

batch_test_petta_to_he :-
    Dirs = [
        '../../hyperon/PeTTa/examples/',
        '../../hyperon/PeTTa/demos/',
        '../../hyperon/hyperon-miner/experiments/',
        '../../hyperon/hyperon-miner/match/',
        '../../hyperon/hyperon-miner/data/',
        '../../hyperon/hyperon-miner/dependent-types/'
    ],
    format("=== Batch PeTTa → HE translation test ===~n~n"),
    batch_dirs_pe(Dirs, 0, 0).

batch_dirs_pe([], Pass, Fail) :-
    Total is Pass + Fail,
    format("~n=== PeTTa→HE Total: ~w/~w parsed+translated, ~w failures ===~n",
           [Pass, Total, Fail]).
batch_dirs_pe([Dir|Ds], Pass, Fail) :-
    (   directory_files(Dir, Files)
    ->  include(is_any_metta, Files, MFs),
        sort(MFs, Sorted),
        length(Sorted, N),
        format("--- ~w (~w files) ---~n", [Dir, N]),
        batch_process_pe(Dir, Sorted, Pass, Fail, P1, F1)
    ;   format("--- ~w (not found, skipping) ---~n", [Dir]),
        P1 = Pass, F1 = Fail
    ),
    batch_dirs_pe(Ds, P1, F1).

is_any_metta(F) :- atom_concat(_, '.metta', F).

batch_process_pe(_, [], P, F, P, F).
batch_process_pe(Dir, [File|Fs], Pass, Fail, POut, FOut) :-
    atom_concat(Dir, File, Path),
    (   catch(
            (   read_metta_file(Path, Atoms),
                length(Atoms, NA),
                maplist(safe_translate_pe, Atoms, _),
                format("  ✓ ~w (~w atoms)~n", [File, NA]),
                P1 is Pass + 1, F1 = Fail
            ),
            Error,
            (   format("  ✗ ~w (~w)~n", [File, Error]),
                P1 = Pass, F1 is Fail + 1
            ))
    ),
    batch_process_pe(Dir, Fs, P1, F1, POut, FOut).
