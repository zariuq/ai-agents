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
:- use_module(library(process),
              [ process_create/3,
                process_wait/2
              ]).
:- use_module(he_to_petta, [translate_term/2 as he_translate_term,
                             translate_term_trusted/2 as he_translate_term_trusted,
                             translate_decl/2 as he_translate_decl,
                             translate_decl_trusted/2 as he_translate_decl_trusted,
                             obsolete_bool_and_rule/1,
                             should_drop_obsolete_bool_and_rule/1]).
:- use_module(petta_to_he, [translate_term/2 as pe_translate_term,
                             translate_term_hyperpose/2 as pe_translate_term_hyperpose,
                             translate_term_ffi_tokens/2 as pe_translate_term_ffi_tokens,
                             translate_term_petta_he/2 as pe_translate_term_petta_he,
                             translate_term_petta_he_hyperpose/2 as pe_translate_term_petta_he_hyperpose,
                             translate_term_extended/2 as pe_translate_term_ext,
                             translate_term_extended_hyperpose/2 as pe_translate_term_ext_hyperpose,
                             translate_term_trusted/2 as pe_translate_term_trusted,
                             translate_decl/2 as pe_translate_decl,
                             translate_decl_hyperpose/2 as pe_translate_decl_hyperpose,
                             translate_decl_ffi_tokens/2 as pe_translate_decl_ffi_tokens,
                             translate_decl_petta_he/2 as pe_translate_decl_petta_he,
                             translate_decl_petta_he_hyperpose/2 as pe_translate_decl_petta_he_hyperpose,
                             translate_decl_extended/2 as pe_translate_decl_ext,
                             translate_decl_extended_hyperpose/2 as pe_translate_decl_ext_hyperpose,
                             translate_decl_trusted/2 as pe_translate_decl_trusted,
                             optimize_term/2 as pe_optimize_term,
                             optimize_decl/2 as pe_optimize_decl,
                             with_helper_context/2 as pe_with_helper_context,
                             rewrite_partial_builtin_value_terms/3 as pe_rewrite_partial_builtin_value_terms,
                             normalize_callable_equality_program/2 as pe_normalize_callable_equality_program,
                             quoted_syntax_fun/1 as pe_quoted_syntax_fun,
                             petta_test_equal_fun/1 as pe_petta_test_equal_fun,
                             petta_test_equal_data_fun/1 as pe_petta_test_equal_data_fun,
                             petta_test_runtime_bool_fun/1 as pe_petta_test_runtime_bool_fun,
                             petta_test_results_fun/1 as pe_petta_test_results_fun,
                             petta_test_results_data_fun/1 as pe_petta_test_results_data_fun,
                             petta_test_bag_fun/1 as pe_petta_test_bag_fun,
                             petta_test_normalize_fun/1 as pe_petta_test_normalize_fun,
                             petta_test_public_term_fun/1 as pe_petta_test_public_term_fun,
                             petta_test_public_syntax_fun/1 as pe_petta_test_public_syntax_fun,
                             petta_if2_fun/1 as pe_petta_if2_fun,
                             petta_lambda_fun/1 as pe_petta_lambda_fun,
                             petta_apply1_fun/1 as pe_petta_apply1_fun,
                             petta_apply2_fun/1 as pe_petta_apply2_fun,
                             petta_bool_and_fun/1 as pe_petta_bool_and_fun,
                             petta_bool_or_fun/1 as pe_petta_bool_or_fun,
                             petta_member_fun/1 as pe_petta_member_fun,
                             petta_ffi_function_call_inversion_fun/1 as pe_petta_ffi_function_call_inversion_fun,
                             petta_lib_petta_helper_decls/2 as pe_petta_lib_petta_helper_decls,
                             test_call_needs_collapse/1 as pe_test_call_needs_collapse,
                             test_call_needs_bag_equality/1 as pe_test_call_needs_bag_equality,
                             petta_state_clear_fun/1 as pe_petta_state_clear_fun,
                             petta_state_set_fun/1 as pe_petta_state_set_fun,
                             petta_state_get_fun/1 as pe_petta_state_get_fun,
                             petta_state_cell_fun/1 as pe_petta_state_cell_fun]).
:- use_module(translator_behavior_contracts, [behavior_contract/2]).

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
    display_source_path(Path, DisplayPath),
    format("; Source: ~w~n~n", [DisplayPath]),
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

translate_file_petta_to_he_hyperpose(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_hyperpose, InPath, OutPath).

translate_file_petta_to_he_ffi_tokens(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_ffi_tokens, InPath, OutPath).

translate_file_petta_to_he_hyperpose_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_hyperpose_raw, InPath, OutPath).

translate_file_petta_to_he_petta_he(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_petta_he, InPath, OutPath).

translate_file_petta_to_he_petta_he_hyperpose(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_petta_he_hyperpose, InPath, OutPath).

translate_file_petta_to_he_petta_he_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_petta_he_raw, InPath, OutPath).

translate_file_petta_to_he_petta_he_hyperpose_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_petta_he_hyperpose_raw, InPath, OutPath).

translate_file_petta_to_he_trusted(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_trusted, InPath, OutPath).

translate_file_petta_to_he_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_raw, InPath, OutPath).

translate_file_petta_to_he_extended(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_extended, InPath, OutPath).

translate_file_petta_to_he_extended_hyperpose(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_extended_hyperpose, InPath, OutPath).

translate_file_petta_to_he_extended_hyperpose_raw(InPath, OutPath) :-
    translate_file_to_path(petta_to_he_extended_hyperpose_raw, InPath, OutPath).

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
translate_file_petta_to_he_mode(InPath, OutPath, hyperpose) :-
    translate_file_petta_to_he_hyperpose(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, ffi_tokens) :-
    translate_file_petta_to_he_ffi_tokens(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, petta_he) :-
    translate_file_petta_to_he_petta_he(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, petta_he_hyperpose) :-
    translate_file_petta_to_he_petta_he_hyperpose(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, trusted) :-
    translate_file_petta_to_he_trusted(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended) :-
    translate_file_petta_to_he_extended(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended_hyperpose) :-
    translate_file_petta_to_he_extended_hyperpose(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, raw) :-
    translate_file_petta_to_he_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, hyperpose_raw) :-
    translate_file_petta_to_he_hyperpose_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, petta_he_raw) :-
    translate_file_petta_to_he_petta_he_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, petta_he_hyperpose_raw) :-
    translate_file_petta_to_he_petta_he_hyperpose_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended_raw) :-
    translate_file_petta_to_he_extended_raw(InPath, OutPath).
translate_file_petta_to_he_mode(InPath, OutPath, extended_hyperpose_raw) :-
    translate_file_petta_to_he_extended_hyperpose_raw(InPath, OutPath).

translate_file_to_path(Direction, InPath, OutPath) :-
    absolute_file_name(InPath, AbsInPath, [relative_to('.'), solutions(first)]),
    absolute_file_name(OutPath, AbsOutPath, [relative_to('.'), solutions(first)]),
    (   materialized_petta_dependency_direction(Direction)
    ->  translate_file_to_path_with_materialized_deps(Direction, AbsInPath, AbsOutPath)
    ;   file_directory_name(AbsOutPath, OutDir),
        make_directory_path(OutDir),
        read_metta_file(AbsInPath, Atoms),
        ensure_he2petta_supported_source(Direction, Atoms),
        length(Atoms, N),
        setup_call_cleanup(
            open(AbsOutPath, write, Stream),
            once((
                write_translation_header(Stream, Direction, AbsInPath, N),
                maybe_write_he2petta_lib_import(Stream, Direction),
                translate_toplevel_atoms(Direction, Atoms, TAtoms),
                relocate_local_module_surfaces(AbsInPath, AbsOutPath, TAtoms, CompatAtoms),
                unitwrap_he2petta_imports(Direction, CompatAtoms, FinalAtoms),
                forall(member(TA, FinalAtoms), write_toplevel_atom(Stream, TA)),
                maybe_materialize_petta_helper_libs(FinalAtoms, AbsOutPath)
            )),
            close(Stream)
        )
    ).

%% When HE2PETTA_LIB_IMPORT is set, file-level HE->PeTTa translation prepends
%% an import of the PeTTa-side HE compatibility library (lib_he) so the
%% artifact is self-contained under native PeTTa. The path is given by the
%% caller relative to the output file location.
maybe_write_he2petta_lib_import(Stream, Direction) :-
    (   he2petta_direction_name(Direction),
        getenv('HE2PETTA_LIB_IMPORT', LibPath),
        LibPath \== ''
    ->  format(Stream, "!(import! &self ~w)~n~n", [LibPath])
    ;   true
    ).

he2petta_direction_name(he_to_petta).
he2petta_direction_name(he_to_petta_trusted).

%% import! returns () in HE but True in PeTTa; wrap the written directive to
%% the HE unit surface. Applied after relocation so module-path rewriting and
%% recursive dependency discovery keep seeing the bare import shape.
unitwrap_he2petta_imports(Direction, Atoms, Out) :-
    (   he2petta_direction_name(Direction)
    ->  maplist(unitwrap_toplevel_import, Atoms, Out)
    ;   Out = Atoms
    ).

%% Native import! itself returns unit now; keep the directive bare so module
%% resolution sees the top-level import shape.
unitwrap_toplevel_import(Atom, Atom).

materialized_petta_dependency_direction(petta_to_he).
materialized_petta_dependency_direction(petta_to_he_hyperpose).
materialized_petta_dependency_direction(petta_to_he_ffi_tokens).
materialized_petta_dependency_direction(petta_to_he_trusted).
materialized_petta_dependency_direction(petta_to_he_raw).
materialized_petta_dependency_direction(petta_to_he_hyperpose_raw).
materialized_petta_dependency_direction(petta_to_he_petta_he).
materialized_petta_dependency_direction(petta_to_he_petta_he_hyperpose).
materialized_petta_dependency_direction(petta_to_he_petta_he_raw).
materialized_petta_dependency_direction(petta_to_he_petta_he_hyperpose_raw).
materialized_petta_dependency_direction(petta_to_he_extended).
materialized_petta_dependency_direction(petta_to_he_extended_hyperpose).
materialized_petta_dependency_direction(petta_to_he_extended_raw).
materialized_petta_dependency_direction(petta_to_he_extended_hyperpose_raw).

translate_file_to_path_with_materialized_deps(Direction, EntrySource, EntryOutPath) :-
    file_directory_name(EntryOutPath, OutDir),
    make_directory_path(OutDir),
    translate_materialized_file_recursive(Direction, EntrySource, EntrySource,
        EntryOutPath, [], _).

translate_materialized_file_recursive(_, _, SourcePath, _, Seen, Seen) :-
    memberchk(SourcePath, Seen), !.
translate_materialized_file_recursive(Direction, EntrySource, SourcePath, OutPath,
                                      SeenIn, SeenOut) :-
    read_metta_file(SourcePath, Atoms),
    ensure_he2petta_supported_source(Direction, Atoms),
    length(Atoms, N),
    translate_toplevel_atoms(Direction, Atoms, TAtoms0),
    rewrite_materialized_module_surfaces(EntrySource, SourcePath, OutPath,
        TAtoms0, TAtoms, Deps),
    file_directory_name(OutPath, OutDir),
    make_directory_path(OutDir),
    setup_call_cleanup(
        open(OutPath, write, Stream),
        (
            write_translation_header(Stream, Direction, SourcePath, N),
            forall(member(TA, TAtoms), write_toplevel_atom(Stream, TA)),
            maybe_materialize_petta_helper_libs(TAtoms, OutPath)
        ),
        close(Stream)
    ),
    SeenMid = [SourcePath|SeenIn],
    translate_materialized_deps_recursive(Direction, EntrySource, SourcePath,
        Deps, SeenMid, SeenOut).

translate_materialized_deps_recursive(_, _, _, [], Seen, Seen).
translate_materialized_deps_recursive(Direction, EntrySource, ParentSource,
                                     [dep(DepSource, DepOutPath)|Deps],
                                     SeenIn, SeenOut) :-
    catch(
        translate_materialized_file_recursive(Direction, EntrySource,
            DepSource, DepOutPath, SeenIn, SeenMid),
        Error,
        rethrow_materialized_dependency_error(ParentSource, DepSource, Error)
    ),
    translate_materialized_deps_recursive(Direction, EntrySource, ParentSource,
        Deps, SeenMid, SeenOut).

rethrow_materialized_dependency_error(ParentSource, DepSource,
                                      error(domain_error(he_core_surface, Surface), _)) :-
    format(atom(Message),
           'while translating dependency ~w imported from ~w',
           [DepSource, ParentSource]),
    throw(error(domain_error(he_core_surface, Surface),
                context(test_on_real_files:translate_materialized_file_recursive/6,
                        Message))).
rethrow_materialized_dependency_error(_, _, Error) :-
    throw(Error).

rewrite_materialized_module_surfaces(EntrySource, SourcePath, OutPath, TAtoms0,
                                     TAtoms, Deps) :-
    rewrite_materialized_module_surfaces_acc(EntrySource, SourcePath, OutPath,
        TAtoms0, [], TAtoms, [], DepPairs),
    sort(DepPairs, Deps).

ensure_he2petta_supported_source(Direction, Atoms) :-
    (   he2petta_direction_name(Direction),
        he2petta_has_doc_surface(Atoms)
    ->  throw(error(domain_error(he_core_surface, doc_surface),
                    context(test_on_real_files:translate_file_to_path/3,
                            'no portable doc-surface translation: @doc/get-doc/help! depend on lane-specific documentation support')))
    ;   true
    ).

he2petta_has_doc_surface(['!', Expr | Rest]) :-
    !,
    (   he2petta_doc_exec_expr(Expr)
    ;   he2petta_has_doc_surface(Rest)
    ).
he2petta_has_doc_surface([['@doc'|_]|_]) :-
    !.
he2petta_has_doc_surface([_|Rest]) :-
    he2petta_has_doc_surface(Rest).

he2petta_doc_exec_expr(['get-doc'|_]).
he2petta_doc_exec_expr(['help!'|_]).

rewrite_materialized_module_surfaces_acc(_, _, _, [], _, [], DepAcc, DepAcc).
rewrite_materialized_module_surfaces_acc(EntrySource, SourcePath, OutPath,
                                         [Atom|Atoms], EnvIn, [TAtom|TAtoms],
                                         DepIn, DepOut) :-
    rewrite_materialized_toplevel_atom(EntrySource, SourcePath, OutPath,
        Atom, EnvIn, TAtom, EnvMid, AtomDeps),
    append(DepIn, AtomDeps, DepMid),
    rewrite_materialized_module_surfaces_acc(EntrySource, SourcePath, OutPath,
        Atoms, EnvMid, TAtoms, DepMid, DepOut).

rewrite_materialized_toplevel_atom(_, SourcePath, _OutPath,
                                   exec(['register-module!', Root]),
                                   EnvIn, TAtom, EnvOut, []) :-
    (   resolve_local_module_dir(SourcePath, Root, ResolvedDir, _Style)
    ->  module_root_name(ResolvedDir, RootName),
        update_module_root_env(RootName, ResolvedDir, EnvIn, EnvOut),
        TAtom = exec('()')
    ;   TAtom = exec(['register-module!', Root]),
        EnvOut = EnvIn
    ), !.
rewrite_materialized_toplevel_atom(EntrySource, SourcePath, OutPath,
                                   exec(['import!', Space, Spec]),
                                   EnvIn, exec(['import!', Space, ModuleName]),
                                   EnvIn, Deps) :-
    (   resolve_materialized_import(SourcePath, EnvIn, Spec, ResolvedFile)
    ->  dependency_output_path(EntrySource, OutPath, ResolvedFile,
            ModuleName, DepOutPath),
        Deps = [dep(ResolvedFile, DepOutPath)]
    ;   ModuleName = Spec,
        Deps = []
    ), !.
rewrite_materialized_toplevel_atom(EntrySource, SourcePath, OutPath,
                                   exec([include, Spec]),
                                   EnvIn, exec([include, ModuleName]),
                                   EnvIn, Deps) :-
    (   resolve_materialized_import(SourcePath, EnvIn, Spec, ResolvedFile)
    ->  dependency_output_path(EntrySource, OutPath, ResolvedFile,
            ModuleName, DepOutPath),
        Deps = [dep(ResolvedFile, DepOutPath)]
    ;   ModuleName = Spec,
        Deps = []
    ), !.
rewrite_materialized_toplevel_atom(_, _, _, Atom, Env, Atom, Env, []).

resolve_materialized_import(SourcePath, _Env, Spec, ResolvedFile) :-
    resolve_local_module_file(SourcePath, Spec, ResolvedFile, _Style), !.
resolve_materialized_import(_, Env, Spec, ResolvedFile) :-
    resolve_registered_module_file(Env, Spec, ResolvedFile, _Style).

dependency_output_path(EntrySource, OutPath, ResolvedFile, ModuleName, DepOutPath) :-
    materialized_dependency_module_name(EntrySource, ResolvedFile, ModuleName),
    file_directory_name(OutPath, OutDir),
    atom_concat(ModuleName, '.metta', DepFile),
    directory_file_path(OutDir, DepFile, DepOutPath).

materialized_dependency_module_name(EntrySource, ResolvedFile, ModuleName) :-
    materialized_dependency_fragment(EntrySource, ResolvedFile, Fragment),
    atom_concat('petta_dep_', Fragment, ModuleName).

materialized_dependency_fragment(EntrySource, ResolvedFile, Fragment) :-
    common_path_base(EntrySource, ResolvedFile, BaseDir),
    relative_file_name(ResolvedFile, BaseDir, RelPath0),
    strip_metta_suffix(RelPath0, RelPath),
    sanitize_module_name_fragment(RelPath, Fragment0),
    normalize_module_fragment(Fragment0, Fragment).

common_path_base(PathA, PathB, BaseDir) :-
    file_directory_name(PathA, DirA),
    file_directory_name(PathB, DirB),
    path_segments(DirA, SegsA),
    path_segments(DirB, SegsB),
    common_prefix_segments(SegsA, SegsB, Prefix),
    segments_to_absolute_dir(Prefix, BaseDir).

path_segments(Path, Segments) :-
    atom_string(Path, PathString),
    split_string(PathString, "/", "", RawSegments),
    exclude(=(""), RawSegments, Segments).

common_prefix_segments([], _, []).
common_prefix_segments(_, [], []).
common_prefix_segments([A|As], [B|Bs], [A|Rest]) :-
    A = B,
    !,
    common_prefix_segments(As, Bs, Rest).
common_prefix_segments(_, _, []).

segments_to_absolute_dir([], '/').
segments_to_absolute_dir(Segments, BaseDir) :-
    atomic_list_concat(Segments, '/', Inner),
    atom_concat('/', Inner, BaseDir).

strip_metta_suffix(Path0, Path) :-
    atom_concat(Path, '.metta', Path0),
    !.
strip_metta_suffix(Path, Path).

sanitize_module_name_fragment(Input, Output) :-
    atom_chars(Input, Chars),
    maplist(sanitize_module_char, Chars, SafeChars),
    atom_chars(Output, SafeChars).

sanitize_module_char(Char, Char) :-
    char_type(Char, alnum),
    !.
sanitize_module_char('_', '_') :- !.
sanitize_module_char('-', '-') :- !.
sanitize_module_char(_, '_').

normalize_module_fragment(Fragment0, Fragment) :-
    atom_chars(Fragment0, Chars0),
    collapse_adjacent_underscores(Chars0, Chars1),
    trim_edge_underscores(Chars1, Chars2),
    (   Chars2 = []
    ->  Fragment = dep
    ;   atom_chars(Fragment, Chars2)
    ).

collapse_adjacent_underscores([], []).
collapse_adjacent_underscores(['_' ,'_'|Rest], Out) :-
    !,
    collapse_adjacent_underscores(['_'|Rest], Out).
collapse_adjacent_underscores([Char|Rest], [Char|Out]) :-
    collapse_adjacent_underscores(Rest, Out).

trim_edge_underscores(Chars0, Chars) :-
    trim_leading_underscores(Chars0, Chars1),
    reverse(Chars1, Rev1),
    trim_leading_underscores(Rev1, Rev2),
    reverse(Rev2, Chars).

trim_leading_underscores(['_'|Rest], Out) :-
    !,
    trim_leading_underscores(Rest, Out).
trim_leading_underscores(Chars, Chars).

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

display_source_path(Path, DisplayPath) :-
    absolute_file_name(Path, AbsPath, [relative_to('.'), solutions(first)]),
    working_directory(Cwd, Cwd),
    atom_concat(Cwd, Rel, AbsPath), !,
    ( Rel = ''
    -> DisplayPath = '.'
    ;  DisplayPath = Rel
    ).
display_source_path(Path, Path).

write_translation_header(Stream, he_to_petta, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from HE to PeTTa (~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, he_to_petta_trusted, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from HE to PeTTa (trusted, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_hyperpose, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (preserve hyperpose, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_ffi_tokens, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (ffi tokens, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_trusted, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (trusted, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_hyperpose_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (preserve hyperpose raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_petta_he, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (PeTTa HE profile, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_petta_he_hyperpose, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (PeTTa HE profile preserve hyperpose, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_petta_he_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (PeTTa HE profile raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_petta_he_hyperpose_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (PeTTa HE profile preserve hyperpose raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_extended, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (extended, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_extended_hyperpose, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (extended preserve hyperpose, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_extended_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (extended raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).
write_translation_header(Stream, petta_to_he_extended_hyperpose_raw, InPath, N) :-
    display_source_path(InPath, DisplayPath),
    format(Stream, "; Translated from PeTTa to HE (extended preserve hyperpose raw, ~w atoms)~n", [N]),
    format(Stream, "; Source: ~w~n~n", [DisplayPath]).

translate_decl_for(he_to_petta, A, TA) :-
    safe_translate_he(A, TA).
translate_decl_for(he_to_petta_trusted, A, TA) :-
    safe_translate_he_trusted(A, TA).
translate_decl_for(petta_to_he, A, TA) :-
    safe_translate_pe(A, TA).
translate_decl_for(petta_to_he_hyperpose, A, TA) :-
    safe_translate_pe_hyperpose(A, TA).
translate_decl_for(petta_to_he_ffi_tokens, A, TA) :-
    safe_translate_pe_ffi_tokens(A, TA).
translate_decl_for(petta_to_he_trusted, A, TA) :-
    safe_translate_pe_trusted(A, TA).
translate_decl_for(petta_to_he_raw, A, TA) :-
    safe_translate_pe_raw(A, TA).
translate_decl_for(petta_to_he_hyperpose_raw, A, TA) :-
    safe_translate_pe_hyperpose_raw(A, TA).
translate_decl_for(petta_to_he_petta_he, A, TA) :-
    safe_translate_pe_petta_he(A, TA).
translate_decl_for(petta_to_he_petta_he_hyperpose, A, TA) :-
    safe_translate_pe_petta_he_hyperpose(A, TA).
translate_decl_for(petta_to_he_petta_he_raw, A, TA) :-
    safe_translate_pe_petta_he_raw(A, TA).
translate_decl_for(petta_to_he_petta_he_hyperpose_raw, A, TA) :-
    safe_translate_pe_petta_he_hyperpose_raw(A, TA).
translate_decl_for(petta_to_he_extended, A, TA) :-
    safe_translate_pe_extended(A, TA).
translate_decl_for(petta_to_he_extended_hyperpose, A, TA) :-
    safe_translate_pe_extended_hyperpose(A, TA).
translate_decl_for(petta_to_he_extended_raw, A, TA) :-
    safe_translate_pe_extended_raw(A, TA).
translate_decl_for(petta_to_he_extended_hyperpose_raw, A, TA) :-
    safe_translate_pe_extended_hyperpose_raw(A, TA).

translate_term_for(he_to_petta, A, TA) :-
    he_translate_term(A, TA).
translate_term_for(he_to_petta_trusted, A, TA) :-
    he_translate_term_trusted(A, TA).
translate_term_for(petta_to_he, A, TA) :-
    pe_translate_term(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_hyperpose, A, TA) :-
    pe_translate_term_hyperpose(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_ffi_tokens, A, TA) :-
    pe_translate_term_ffi_tokens(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_trusted, A, TA) :-
    pe_translate_term_trusted(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_raw, A, TA) :-
    pe_translate_term(A, TA).
translate_term_for(petta_to_he_hyperpose_raw, A, TA) :-
    pe_translate_term_hyperpose(A, TA).
translate_term_for(petta_to_he_petta_he, A, TA) :-
    pe_translate_term_petta_he(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_petta_he_hyperpose, A, TA) :-
    pe_translate_term_petta_he_hyperpose(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_petta_he_raw, A, TA) :-
    pe_translate_term_petta_he(A, TA).
translate_term_for(petta_to_he_petta_he_hyperpose_raw, A, TA) :-
    pe_translate_term_petta_he_hyperpose(A, TA).
translate_term_for(petta_to_he_extended, A, TA) :-
    pe_translate_term_ext(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_extended_hyperpose, A, TA) :-
    pe_translate_term_ext_hyperpose(A, Raw),
    pe_optimize_term(Raw, TA).
translate_term_for(petta_to_he_extended_raw, A, TA) :-
    pe_translate_term_ext(A, TA).
translate_term_for(petta_to_he_extended_hyperpose_raw, A, TA) :-
    pe_translate_term_ext_hyperpose(A, TA).

translate_toplevel_atoms(Direction, Atoms, TAtoms) :-
    petta_to_he_direction(Direction),
    !,
    pe_with_helper_context(Atoms,
        ( translate_toplevel_atoms_acc(Direction, Atoms, Atoms, TAtoms0),
          postprocess_toplevel_atoms(Direction, Atoms, TAtoms0, TAtoms)
        )).
translate_toplevel_atoms(Direction, Atoms, TAtoms) :-
    (   he2petta_direction_name(Direction)
    ->  he_to_petta:rename_native_reserved_heads(Atoms, Atoms1)
    ;   Atoms1 = Atoms
    ),
    (   he2petta_direction_name(Direction)
    ->  SourceCtx = ctx(Atoms1, [])
    ;   SourceCtx = Atoms1
    ),
    translate_toplevel_atoms_acc(Direction, SourceCtx, Atoms1, TAtoms0),
    postprocess_toplevel_atoms(Direction, Atoms1, TAtoms0, TAtoms).

source_nil_surface('()').
source_nil_surface([]).

translate_toplevel_atoms_acc(_, _, [], []).
%% File translation keeps the same split: the portable lanes can canonicalize
%% well-known recursive helpers, but the PeTTa --he profile is closer to a
%% source-preserving runtime target and should retain those definitions.
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['map-flat', F, Nil], Nil],
                             ['=', ['map-flat', F, [cons, X, Xs]],
                              [cons, [F, X], ['map-flat', F, Xs]]]
                             | Rest],
                            [plain(['=', ['map-flat', F, '$list'],
                                     ['map-atom', '$list', '$item', [Apply1, F, '$item']]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply1_fun(Apply1),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['map-flat2', [Nil, F]], Nil],
                             ['=', ['map-flat2', [[cons, X, Xs], F]],
                              [cons, [F, X], ['map-flat2', [Xs, F]]]]
                             | Rest],
                            [plain(['=', ['map-flat2', '$pair'],
                                     [let, ['$list', F], '$pair',
                                      ['map-atom', '$list', '$item', [Apply1, F, '$item']]]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply1_fun(Apply1),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['map-flat3', [F, Nil]], Nil],
                             ['=', ['map-flat3', [F, [cons, X, Xs]]],
                              [cons, [F, X], ['map-flat3', [F, Xs]]]]
                             | Rest],
                            [plain(['=', ['map-flat3', '$pairq'],
                                     Body])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply1_fun(Apply1),
    file_map_flat3_exprdata_body(Apply1, F, Body),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['map-flat4', [V, [F, Nil]]], Nil],
                             ['=', ['map-flat4', [V, [F, [cons, X, Xs]]]],
                              [cons, [F, X], ['map-flat4', [V, [F, Xs]]]]]
                             | Rest],
                            [plain(['=', ['map-flat4', '$pairq'],
                                     Body])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply1_fun(Apply1),
    file_map_flat4_exprdata_body(Apply1, F, V, Body),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['map-nested', F, Nil], Nil],
                             ['=', ['map-nested', F, [cons, X, Xs]],
                              [if, ['is-expr', X],
                               [cons, ['map-nested', F, X], ['map-nested', F, Xs]],
                               [cons, [F, X], ['map-nested', F, Xs]]]]
                             | Rest],
                            [plain(['=', ['map-nested', F, '$list'],
                                     ['map-atom', '$list', '$item',
                                      [if, ['==', ['get-metatype', '$item'], 'Expression'],
                                       ['map-nested', F, '$item'],
                                       [Apply1, F, '$item']]]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply1_fun(Apply1),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['fold-flat', F, Init, Nil], Init],
                             ['=', ['fold-flat', F, Init, [cons, X, Xs]],
                              ['fold-flat', F, [F, Init, X], Xs]]
                             | Rest],
                            [plain(['=', ['fold-flat', F, Init, '$list'],
                                     ['foldl-atom', '$list', Init, '$acc', '$item',
                                      [Apply2, F, '$acc', '$item']]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply2_fun(Apply2),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['fold-nested', F, Init, Nil], Init],
                             ['=', ['fold-nested', F, Init, [cons, X, Xs]],
                              [if, ['is-expr', X],
                               ['fold-nested', F, ['fold-nested', F, Init, X], Xs],
                               ['fold-nested', F, [F, Init, X], Xs]]]
                             | Rest],
                            [plain(['=', ['fold-nested', F, Init, '$list'],
                                     ['foldl-atom', '$list', Init, '$acc', '$item',
                                      [if, ['==', ['get-metatype', '$item'], 'Expression'],
                                       ['fold-nested', F, '$acc', '$item'],
                                       [Apply2, F, '$acc', '$item']]]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    source_nil_surface(Nil),
    pe_petta_apply2_fun(Apply2),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['/==\\', A, B], ['/?\\', '==', A, B]]
                             | Rest],
                            [plain(['=', ['/==\\', A, B],
                                     [let, '$intersection',
                                      ['intersection-atom', A, B],
                                      '$intersection']])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['\\==', A, B], ['\\?', '==', A, B]]
                             | Rest],
                            [plain(['=', ['\\==', A, B],
                                     [let, '$difference',
                                      ['subtraction-atom', A, B],
                                      '$difference']])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['\\==/', A, B], ['\\?/', '==', A, B]]
                             | Rest],
                            [plain(['=', ['\\==/', A, B],
                                     [let, '$difference',
                                      ['subtraction-atom', A, B],
                                      ['union-atom', '$difference', B]]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms,
                            [['=', ['.:', F1, F2, Arg1, Arg2],
                              [F1, [F2, Arg1, Arg2]]]
                             | Rest],
                            [plain(['=', ['.:', F1, F2, Arg1, Arg2],
                                     [F1, [F2, Arg1, Arg2]]])
                             | TRest]) :-
    petta_to_he_direction(Direction),
    \+ petta_he_profile_direction(Direction),
    !,
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms, ['!' , Expr | Rest], [exec(TExpr) | TRest]) :-
    translate_exec_term_for(Direction, SourceAtoms, Expr, TExpr),
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms, [A | Rest], [plain(TA) | TRest]) :-
    translate_toplevel_atom(Direction, A, TA),
    he2petta_extend_seen_funs(SourceAtoms, A, NextSourceAtoms),
    translate_toplevel_atoms_acc(Direction, NextSourceAtoms, Rest, TRest).

translate_exec_term_for(he_to_petta, ctx(AllAtoms, SeenFuns), A, TA) :-
    he2petta_all_defined_funs(AllAtoms, AllFuns),
    subtract(AllFuns, SeenFuns, FutureFuns),
    he_to_petta:translate_term_with_fun_context(SeenFuns, FutureFuns, A, TA0),
    he2petta_wrap_exec_let_bindings(TA0, TA).
translate_exec_term_for(he_to_petta_trusted, ctx(AllAtoms, SeenFuns), A, TA) :-
    he2petta_all_defined_funs(AllAtoms, AllFuns),
    subtract(AllFuns, SeenFuns, FutureFuns),
    he_to_petta:translate_term_trusted_with_fun_context(SeenFuns, FutureFuns, A, TA0),
    he2petta_wrap_exec_let_bindings(TA0, TA).
translate_exec_term_for(Direction, _SourceAtoms, A, TA) :-
    translate_term_for(Direction, A, TA).

he2petta_all_defined_funs(Atoms, Funs) :-
    findall(Fun,
            he2petta_source_defined_marker_or_decl(Atoms, Fun),
            Funs0),
    sort(Funs0, Funs).

he2petta_source_defined_marker_or_decl(Atoms, Fun) :-
    member(Atom, Atoms),
    he2petta_defined_fun_atom(Atom, Fun).
he2petta_source_defined_marker_or_decl(Atoms, Fun) :-
    member(['source-defined-function', Fun], Atoms).

he2petta_wrap_exec_let_bindings([quote|Payload], [quote|Payload]) :- !.
he2petta_wrap_exec_let_bindings([let, Pat, Val, Body],
                                [let, Pat, WrappedVal, TBody]) :-
    !,
    he2petta_wrap_exec_let_bindings(Val, TVal),
    (   he2petta_generated_temp_var(Pat)
    ->  WrappedVal = TVal
    ;   WrappedVal = ['match-template-eval', TVal]
    ),
    he2petta_wrap_exec_let_bindings(Body, TBody).
he2petta_wrap_exec_let_bindings(['let*', Bindings, Body],
                                ['let*', TBindings, TBody]) :-
    !,
    maplist(he2petta_wrap_exec_let_binding, Bindings, TBindings),
    he2petta_wrap_exec_let_bindings(Body, TBody).
he2petta_wrap_exec_let_bindings(List, TList) :-
    is_list(List),
    !,
    maplist(he2petta_wrap_exec_let_bindings, List, TList).
he2petta_wrap_exec_let_bindings(X, X).

he2petta_wrap_exec_let_binding([Pat, Val], [Pat, WrappedVal]) :-
    he2petta_wrap_exec_let_bindings(Val, TVal),
    (   he2petta_generated_temp_var(Pat)
    ->  WrappedVal = TVal
    ;   WrappedVal = ['match-template-eval', TVal]
    ).
he2petta_wrap_exec_let_binding(Binding, Binding).

he2petta_generated_temp_var(Pat) :-
    atom(Pat),
    atom_concat('$__tr_', _, Pat).

he2petta_extend_seen_funs(ctx(AllAtoms, Seen0), Atom, ctx(AllAtoms, Seen)) :-
    !,
    (   he2petta_defined_fun_atom(Atom, Fun),
        \+ memberchk(Fun, Seen0)
    ->  append(Seen0, [Fun], Seen)
    ;   Seen = Seen0
    ).
he2petta_extend_seen_funs(SourceAtoms, _Atom, SourceAtoms).

he2petta_defined_fun_atom(['=', Head, _], Fun) :-
    he2petta_defined_fun_head(Head, Fun).
he2petta_defined_fun_atom([':', Head, _], Fun) :-
    he2petta_defined_fun_head(Head, Fun).

he2petta_defined_fun_head([Head|_], Fun) :-
    !,
    he_to_petta:base_head_symbol(Head, Fun).
he2petta_defined_fun_head(Head, Fun) :-
    he_to_petta:base_head_symbol(Head, Fun).

file_map_flat3_exprdata_body(Apply1, F,
                             [let, ['$head', '$tail'], ['decons-atom', '$pairq'],
                              [if, ['==', '$head', quote],
                               QuoteBranch,
                               RawBranch]]) :-
    QuoteBranch =
        [let, ['$pair', '$quote-tail'], ['decons-atom', '$tail'],
         [let, [F, '$tail1'], ['decons-atom', '$pair'],
          [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
           ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]],
    RawBranch =
        [let, [F, '$tail1'], ['decons-atom', '$pairq'],
         [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
          ['map-atom', '$list', '$item', [Apply1, F, '$item']]]].

file_map_flat4_exprdata_body(Apply1, F, V,
                             [let, ['$head', '$tail'], ['decons-atom', '$pairq'],
                              [if, ['==', '$head', quote],
                               QuoteBranch,
                               RawBranch]]) :-
    QuoteBranch =
        [let, ['$pair', '$quote-tail'], ['decons-atom', '$tail'],
         [let, [V, '$tail0'], ['decons-atom', '$pair'],
          [let, ['$inner', '$tailv'], ['decons-atom', '$tail0'],
           [let, [F, '$tail1'], ['decons-atom', '$inner'],
            [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
             ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]]]],
    RawBranch =
        [let, [V, '$tail0'], ['decons-atom', '$pairq'],
         [let, ['$inner', '$tailv'], ['decons-atom', '$tail0'],
          [let, [F, '$tail1'], ['decons-atom', '$inner'],
           [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
            ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]]].

translate_toplevel_atom(Direction, A, TA) :-
    (   A = ['=', _, _]
    ;   A = [':', _, _]
    ),
    !,
    translate_decl_for(Direction, A, TA).
%% HE->PeTTa: plain top-level facts are stored data that upstream never
%% evaluates; they pass through verbatim (renaming already ran as a pre-pass).
translate_toplevel_atom(Direction, A, A) :-
    he2petta_direction_name(Direction), !.
translate_toplevel_atom(Direction, A, TA) :-
    translate_term_for(Direction, A, TA).

postprocess_toplevel_atoms(he_to_petta, Atoms, TAtoms0, TAtoms) :-
    (   should_drop_obsolete_bool_and_rule(Atoms)
    ->  exclude(is_obsolete_bool_and_item, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).
postprocess_toplevel_atoms(he_to_petta_trusted, Atoms, TAtoms0, TAtoms) :-
    postprocess_toplevel_atoms(he_to_petta, Atoms, TAtoms0, TAtoms).
postprocess_toplevel_atoms(Direction, Atoms, TAtoms0, TAtoms) :-
    petta_to_he_direction(Direction),
    maybe_prepend_petta_compat_items(Direction, Atoms, TAtoms0, TAtoms), !.
postprocess_toplevel_atoms(_, _, TAtoms, TAtoms).

is_obsolete_bool_and_item(plain(Expr)) :-
    obsolete_bool_and_rule(Expr).
is_obsolete_bool_and_item(_) :-
    fail.

petta_to_he_direction(petta_to_he).
petta_to_he_direction(petta_to_he_hyperpose).
petta_to_he_direction(petta_to_he_ffi_tokens).
petta_to_he_direction(petta_to_he_trusted).
petta_to_he_direction(petta_to_he_raw).
petta_to_he_direction(petta_to_he_hyperpose_raw).
petta_to_he_direction(petta_to_he_petta_he).
petta_to_he_direction(petta_to_he_petta_he_hyperpose).
petta_to_he_direction(petta_to_he_petta_he_raw).
petta_to_he_direction(petta_to_he_petta_he_hyperpose_raw).
petta_to_he_direction(petta_to_he_extended).
petta_to_he_direction(petta_to_he_extended_hyperpose).
petta_to_he_direction(petta_to_he_extended_raw).
petta_to_he_direction(petta_to_he_extended_hyperpose_raw).

petta_he_profile_direction(petta_to_he_petta_he).
petta_he_profile_direction(petta_to_he_petta_he_hyperpose).
petta_he_profile_direction(petta_to_he_petta_he_raw).
petta_he_profile_direction(petta_to_he_petta_he_hyperpose_raw).

maybe_prepend_petta_compat_items(Direction, SourceAtoms, TAtoms0, TAtoms) :-
    maybe_rewrite_partial_builtin_value_items(TAtoms0, TAtoms1),
    maybe_normalize_callable_equality_items(TAtoms1, TAtoms2),
    maybe_rewrite_builtin_test_items(Direction, SourceAtoms, TAtoms2, TAtoms3),
    maybe_prepend_append_compat_items(SourceAtoms, TAtoms3, TAtoms4),
    maybe_prepend_petta_lib_petta_compat_items(Direction, SourceAtoms, TAtoms4, TAtoms5),
    maybe_prepend_petta_state_compat_items(SourceAtoms, TAtoms5, TAtoms6),
    maybe_prepend_quote_compat_items(SourceAtoms, TAtoms6, TAtoms7),
    maybe_prepend_length_compat_items(Direction, SourceAtoms, TAtoms7, TAtoms8),
    TAtoms = TAtoms8.

maybe_rewrite_partial_builtin_value_items(Items0, Items) :-
    item_payloads(Items0, Terms0),
    pe_rewrite_partial_builtin_value_terms(Terms0, HelperDecls, Terms),
    wrap_plain_items(HelperDecls, HelperItems),
    rewrite_items_with_payloads(Items0, Terms, RewrittenItems),
    append(HelperItems, RewrittenItems, Items).

maybe_normalize_callable_equality_items(Items0, Items) :-
    item_payloads(Items0, Terms0),
    pe_normalize_callable_equality_program(Terms0, Terms),
    rewrite_items_with_payloads(Items0, Terms, Items).

item_payloads([], []).
item_payloads([Item|Items], [Term|Terms]) :-
    item_payload(Item, Term),
    item_payloads(Items, Terms).

rewrite_items_with_payloads([], [], []).
rewrite_items_with_payloads([exec(_)|Items], [Term|Terms], [exec(Term)|Rewritten]) :-
    rewrite_items_with_payloads(Items, Terms, Rewritten).
rewrite_items_with_payloads([plain(_)|Items], [Term|Terms], [plain(Term)|Rewritten]) :-
    rewrite_items_with_payloads(Items, Terms, Rewritten).

maybe_prepend_append_compat_items(SourceAtoms, TAtoms0, TAtoms) :-
    (   source_program_uses_append(SourceAtoms),
        \+ source_program_defines_append(SourceAtoms)
    ->  petta_append_compat_items(CompatItems),
        append(CompatItems, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).

maybe_prepend_petta_lib_petta_compat_items(Direction, SourceAtoms, TAtoms0, TAtoms) :-
    translated_items_need_lib_petta_helpers(Direction, SourceAtoms, TAtoms0, HelperKeys),
    (   HelperKeys \= []
    ->  (   lib_petta_helpers_can_import(HelperKeys)
        ->  petta_lib_petta_import_items(CompatItems)
        ;   petta_lib_petta_inline_items(HelperKeys, CompatItems)
        ),
        append(CompatItems, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).

maybe_prepend_petta_state_compat_items(SourceAtoms, TAtoms0, TAtoms) :-
    (   translated_items_use_petta_state_helper(TAtoms0),
        \+ source_program_defines_petta_state_helper(SourceAtoms)
    ->  petta_state_compat_items(CompatItems),
        append(CompatItems, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).

maybe_prepend_quote_compat_items(SourceAtoms, TAtoms0, TAtoms) :-
    (   translated_items_use_quoted_syntax(TAtoms0),
        \+ source_program_defines_quoted_syntax(SourceAtoms)
    ->  petta_quote_compat_items(CompatItems),
        append(CompatItems, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).

maybe_prepend_length_compat_items(Direction, SourceAtoms, TAtoms0, TAtoms) :-
    (   source_program_uses_length(SourceAtoms),
        \+ source_program_defines_length(SourceAtoms)
    ->  petta_length_compat_items(Direction, CompatItems),
        append(CompatItems, TAtoms0, TAtoms)
    ;   TAtoms = TAtoms0
    ).

maybe_rewrite_builtin_test_items(Direction, _SourceAtoms, TAtoms0, TAtoms) :-
    petta_he_profile_direction(Direction),
    !,
    TAtoms = TAtoms0.
maybe_rewrite_builtin_test_items(_Direction, SourceAtoms, TAtoms0, TAtoms) :-
    (   source_program_defines_test(SourceAtoms)
    ->  TAtoms = TAtoms0
    ;   maplist(rewrite_builtin_test_item, TAtoms0, TAtoms)
    ).

source_program_uses_length(Term) :-
    is_list(Term),
    (   Term = [length, _]
    ;   member(Subterm, Term),
        source_program_uses_length(Subterm)
    ).

source_program_uses_length(_) :-
    fail.

source_program_uses_append(Term) :-
    is_list(Term),
    (   Term = [append, _, _]
    ;   member(Subterm, Term),
        source_program_uses_append(Subterm)
    ).

source_program_uses_append(_) :-
    fail.

source_program_uses_second_from_pair(Term) :-
    is_list(Term),
    (   Term = ['second-from-pair', _]
    ;   member(Subterm, Term),
        source_program_uses_second_from_pair(Subterm)
    ).

source_program_uses_second_from_pair(_) :-
    fail.

source_program_uses_is_member(Term) :-
    is_list(Term),
    (   Term = ['is-member', _, _]
    ;   member(Subterm, Term),
        source_program_uses_is_member(Subterm)
    ).

source_program_uses_is_member(_) :-
    fail.

source_program_uses_reverse(Term) :-
    is_list(Term),
    (   Term = [reverse, _]
    ;   member(Subterm, Term),
        source_program_uses_reverse(Subterm)
    ).

source_program_uses_reverse(_) :-
    fail.

source_program_uses_last(Term) :-
    is_list(Term),
    (   Term = [last, _]
    ;   member(Subterm, Term),
        source_program_uses_last(Subterm)
    ).

source_program_uses_last(_) :-
    fail.

source_program_uses_foldl(Term) :-
    is_list(Term),
    (   Term = [foldl, _, _, _]
    ;   member(Subterm, Term),
        source_program_uses_foldl(Subterm)
    ).

source_program_uses_foldl(_) :-
    fail.

source_program_uses_min(Term) :-
    is_list(Term),
    (   Term = [min, _, _]
    ;   member(Subterm, Term),
        source_program_uses_min(Subterm)
    ).

source_program_uses_min(_) :-
    fail.

source_program_uses_max(Term) :-
    is_list(Term),
    (   Term = [max, _, _]
    ;   member(Subterm, Term),
        source_program_uses_max(Subterm)
    ).

source_program_uses_max(_) :-
    fail.

source_program_uses_alpha_unique_atom(Term) :-
    is_list(Term),
    (   Term = ['alpha-unique-atom', _]
    ;   member(Subterm, Term),
        source_program_uses_alpha_unique_atom(Subterm)
    ).

source_program_uses_alpha_unique_atom(_) :-
    fail.

source_program_uses_quote(Term) :-
    is_list(Term),
    (   Term = [quote, _]
    ;   member(Subterm, Term),
        source_program_uses_quote(Subterm)
    ).

source_program_uses_quote(_) :-
    fail.

translated_items_use_quoted_syntax(Items) :-
    is_list(Items),
    member(Item, Items),
    item_payload(Item, Term),
    term_uses_quoted_syntax(Term), !.

term_uses_quoted_syntax(Term) :-
    is_list(Term),
    pe_quoted_syntax_fun(QuoteFun),
    (   Term = [QuoteFun|_]
    ;   member(Subterm, Term),
        term_uses_quoted_syntax(Subterm)
    ).

term_uses_quoted_syntax(_) :-
    fail.

translated_items_use_petta_state_helper(Items) :-
    is_list(Items),
    member(Item, Items),
    item_payload(Item, Term),
    term_uses_petta_state_helper(Term), !.

term_uses_petta_state_helper(Term) :-
    is_list(Term),
    (   petta_state_helper_call(Term)
    ;   member(Subterm, Term),
        term_uses_petta_state_helper(Subterm)
    ).

term_uses_petta_state_helper(_) :-
    fail.

petta_state_helper_call([Head|_]) :-
    atom(Head),
    (   pe_petta_state_clear_fun(Head)
    ;   pe_petta_state_set_fun(Head)
    ;   pe_petta_state_get_fun(Head)
    ).

item_payload(exec(Term), Term).
item_payload(plain(Term), Term).

translated_items_need_lib_petta_helpers(Direction, SourceAtoms, Items, HelperKeys) :-
    findall(Key,
            translated_items_need_lib_petta_helper(Direction, SourceAtoms, Items, Key),
            RawKeys),
    helper_key_closure(RawKeys, HelperKeys).

helper_key_closure(Keys0, Keys) :-
    sort(Keys0, Seed),
    helper_key_closure_fixpoint(Seed, Keys).

helper_key_closure_fixpoint(Keys0, Keys) :-
    findall(Dep,
            ( member(Key, Keys0),
              helper_key_dependency(Key, Dep)
            ),
            RawDeps),
    append(Keys0, RawDeps, Keys1),
    sort(Keys1, Sorted),
    (   Sorted == Keys0
    ->  Keys = Sorted
    ;   helper_key_closure_fixpoint(Sorted, Keys)
    ).

helper_key_dependency(apply2, apply1).
helper_key_dependency(apply2, lambda).
helper_key_dependency(apply1, lambda).
helper_key_dependency(test_equal, test_public).
helper_key_dependency(test_equal_data, test_public).
helper_key_dependency(test_results, test_public).
helper_key_dependency(test_results_data, test_public).
helper_key_dependency(test_bag, test_public).

translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, second_from_pair) :-
    source_program_uses_second_from_pair(SourceAtoms),
    \+ source_program_defines_second_from_pair(SourceAtoms).
translated_items_need_lib_petta_helper(Direction, SourceAtoms, _Items, is_member) :-
    \+ petta_he_profile_direction(Direction),
    source_program_uses_is_member(SourceAtoms),
    \+ source_program_defines_is_member(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, reverse) :-
    source_program_uses_reverse(SourceAtoms),
    \+ source_program_defines_reverse(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, last) :-
    source_program_uses_last(SourceAtoms),
    \+ source_program_defines_last(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, foldl) :-
    source_program_uses_foldl(SourceAtoms),
    \+ source_program_defines_foldl(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, min) :-
    source_program_uses_min(SourceAtoms),
    \+ source_program_defines_min(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, max) :-
    source_program_uses_max(SourceAtoms),
    \+ source_program_defines_max(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, alpha_unique_atom) :-
    source_program_uses_alpha_unique_atom(SourceAtoms),
    \+ source_program_defines_alpha_unique_atom(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_equal) :-
    translated_items_use_named_helper(Items, pe_petta_test_equal_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_equal_data) :-
    translated_items_use_named_helper(Items, pe_petta_test_equal_data_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_runtime_bool) :-
    translated_items_use_named_helper(Items, pe_petta_test_runtime_bool_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_results) :-
    translated_items_use_named_helper(Items, pe_petta_test_results_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_results_data) :-
    translated_items_use_named_helper(Items, pe_petta_test_results_data_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_bag) :-
    translated_items_use_named_helper(Items, pe_petta_test_bag_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_public) :-
    (   translated_items_use_named_helper(Items, pe_petta_test_equal_fun)
    ;   translated_items_use_named_helper(Items, pe_petta_test_equal_data_fun)
    ;   translated_items_use_named_helper(Items, pe_petta_test_runtime_bool_fun)
    ;   translated_items_use_named_helper(Items, pe_petta_test_results_fun)
    ;   translated_items_use_named_helper(Items, pe_petta_test_results_data_fun)
    ;   translated_items_use_named_helper(Items, pe_petta_test_bag_fun)
    ).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, alpha_equal_eval) :-
    translated_items_use_named_helper(Items, petta_to_he:petta_alpha_equal_eval_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, runtime_call) :-
    translated_items_use_named_helper(Items, petta_to_he:petta_runtime_call_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, runtime_eval) :-
    translated_items_use_named_helper(Items, petta_to_he:petta_runtime_eval_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, runtime_reduce) :-
    translated_items_use_named_helper(Items, petta_to_he:petta_runtime_reduce_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, lambda) :-
    translated_items_use_named_helper(Items, pe_petta_lambda_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, apply1) :-
    translated_items_use_named_helper(Items, pe_petta_apply1_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, apply2) :-
    translated_items_use_named_helper(Items, pe_petta_apply2_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, bool_and) :-
    translated_items_use_named_helper(Items, pe_petta_bool_and_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, bool_or) :-
    translated_items_use_named_helper(Items, pe_petta_bool_or_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, if2) :-
    translated_items_use_named_helper(Items, pe_petta_if2_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, member) :-
    translated_items_use_named_helper(Items, pe_petta_member_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, ffi_function_call_inversion) :-
    translated_items_use_named_helper(Items, pe_petta_ffi_function_call_inversion_fun).

translated_items_use_named_helper(Items, HelperPred) :-
    call(HelperPred, HelperName),
    is_list(Items),
    member(Item, Items),
    item_payload(Item, Term),
    term_uses_named_head(Term, HelperName),
    !.

term_uses_named_head(Term, HelperName) :-
    is_list(Term),
    (   Term = [HelperName|_]
    ;   member(Subterm, Term),
        term_uses_named_head(Subterm, HelperName)
    ).

term_uses_named_head(_, _) :-
    fail.

lib_petta_helpers_can_import(HelperKeys) :-
    \+ memberchk(test_public, HelperKeys),
    \+ memberchk(test_equal, HelperKeys),
    \+ memberchk(test_equal_data, HelperKeys),
    \+ memberchk(test_runtime_bool, HelperKeys),
    \+ memberchk(test_results, HelperKeys),
    \+ memberchk(test_results_data, HelperKeys),
    \+ memberchk(test_bag, HelperKeys),
    \+ memberchk(alpha_equal_eval, HelperKeys),
    \+ memberchk(runtime_call, HelperKeys),
    \+ memberchk(runtime_eval, HelperKeys),
    \+ memberchk(runtime_reduce, HelperKeys),
    \+ memberchk(lambda, HelperKeys),
    \+ memberchk(apply1, HelperKeys),
    \+ memberchk(apply2, HelperKeys),
    \+ memberchk(if2, HelperKeys),
    \+ memberchk(bool_and, HelperKeys),
    \+ memberchk(bool_or, HelperKeys),
    \+ memberchk(member, HelperKeys),
    maplist(lib_petta_helper_uses_default_names, HelperKeys).

lib_petta_helper_uses_default_names(second_from_pair).
lib_petta_helper_uses_default_names(is_member).
lib_petta_helper_uses_default_names(reverse).
lib_petta_helper_uses_default_names(last).
lib_petta_helper_uses_default_names(foldl).
lib_petta_helper_uses_default_names(min).
lib_petta_helper_uses_default_names(max).
lib_petta_helper_uses_default_names(alpha_unique_atom).
lib_petta_helper_uses_default_names(test_public) :-
    pe_petta_test_public_term_fun('petta-public-term'),
    pe_petta_test_public_syntax_fun('petta-public-syntax').
lib_petta_helper_uses_default_names(test_equal) :-
    pe_petta_test_equal_fun('petta-test-equal').
lib_petta_helper_uses_default_names(test_equal_data) :-
    pe_petta_test_equal_data_fun('petta-test-equal-data').
lib_petta_helper_uses_default_names(test_runtime_bool) :-
    pe_petta_test_runtime_bool_fun('petta-test-runtime-bool').
lib_petta_helper_uses_default_names(test_results) :-
    pe_petta_test_results_fun('petta-test-results'),
    pe_petta_test_normalize_fun('petta-normalize-results').
lib_petta_helper_uses_default_names(test_results_data) :-
    pe_petta_test_results_data_fun('petta-test-results-data'),
    pe_petta_test_normalize_fun('petta-normalize-results').
lib_petta_helper_uses_default_names(test_bag) :-
    pe_petta_test_bag_fun('petta-test-bag-equal').
lib_petta_helper_uses_default_names(alpha_equal_eval) :-
    petta_to_he:petta_alpha_equal_eval_fun('petta-alpha-equal-eval').
lib_petta_helper_uses_default_names(runtime_call) :-
    petta_to_he:petta_runtime_call_fun('petta-runtime-call').
lib_petta_helper_uses_default_names(runtime_eval) :-
    petta_to_he:petta_runtime_eval_fun('petta-runtime-eval').
lib_petta_helper_uses_default_names(runtime_reduce) :-
    petta_to_he:petta_runtime_reduce_fun('petta-runtime-reduce').
lib_petta_helper_uses_default_names(lambda) :-
    pe_petta_lambda_fun('petta-lambda').
lib_petta_helper_uses_default_names(apply1) :-
    pe_petta_apply1_fun('petta-apply1'),
    pe_petta_lambda_fun('petta-lambda').
lib_petta_helper_uses_default_names(apply2) :-
    pe_petta_apply2_fun('petta-apply2'),
    pe_petta_apply1_fun('petta-apply1'),
    pe_petta_lambda_fun('petta-lambda').
lib_petta_helper_uses_default_names(bool_and) :-
    pe_petta_bool_and_fun('petta-bool-and').
lib_petta_helper_uses_default_names(bool_or) :-
    pe_petta_bool_or_fun('petta-bool-or').
lib_petta_helper_uses_default_names(if2) :-
    pe_petta_if2_fun('petta-if2').
lib_petta_helper_uses_default_names(member) :-
    pe_petta_member_fun('petta-member').
lib_petta_helper_uses_default_names(ffi_function_call_inversion) :-
    pe_petta_ffi_function_call_inversion_fun('petta-ffi-function-call-inversion').

source_program_defines_length([['=', [length|_], _]|_]) :- !.
source_program_defines_length([_|Rest]) :-
    source_program_defines_length(Rest).

source_program_defines_append([['=', [append|_], _]|_]) :- !.
source_program_defines_append([_|Rest]) :-
    source_program_defines_append(Rest).

source_program_defines_second_from_pair([['=', ['second-from-pair'|_], _]|_]) :- !.
source_program_defines_second_from_pair([_|Rest]) :-
    source_program_defines_second_from_pair(Rest).

source_program_defines_is_member([['=', ['is-member'|_], _]|_]) :- !.
source_program_defines_is_member([_|Rest]) :-
    source_program_defines_is_member(Rest).

source_program_defines_reverse([['=', [reverse|_], _]|_]) :- !.
source_program_defines_reverse([_|Rest]) :-
    source_program_defines_reverse(Rest).

source_program_defines_last([['=', [last|_], _]|_]) :- !.
source_program_defines_last([_|Rest]) :-
    source_program_defines_last(Rest).

source_program_defines_foldl([['=', [foldl|_], _]|_]) :- !.
source_program_defines_foldl([_|Rest]) :-
    source_program_defines_foldl(Rest).

source_program_defines_min([['=', [min|_], _]|_]) :- !.
source_program_defines_min([_|Rest]) :-
    source_program_defines_min(Rest).

source_program_defines_max([['=', [max|_], _]|_]) :- !.
source_program_defines_max([_|Rest]) :-
    source_program_defines_max(Rest).

source_program_defines_alpha_unique_atom([['=', ['alpha-unique-atom'|_], _]|_]) :- !.
source_program_defines_alpha_unique_atom([_|Rest]) :-
    source_program_defines_alpha_unique_atom(Rest).

source_program_defines_quoted_syntax([['=', [Head|_], _]|_]) :-
    pe_quoted_syntax_fun(Head), !.
source_program_defines_quoted_syntax([_|Rest]) :-
    source_program_defines_quoted_syntax(Rest).

source_program_defines_petta_state_helper([['=', [Head|_], _]|_]) :-
    atom(Head),
    (   pe_petta_state_clear_fun(Head)
    ;   pe_petta_state_set_fun(Head)
    ;   pe_petta_state_get_fun(Head)
    ), !.
source_program_defines_petta_state_helper([_|Rest]) :-
    source_program_defines_petta_state_helper(Rest).

source_program_defines_test([['=', [test|_], _]|_]) :- !.
source_program_defines_test([_|Rest]) :-
    source_program_defines_test(Rest).

petta_append_compat_items([
    plain(['=', [append, '()', '$ys'], '$ys']),
    plain(['=', [append, '$xs', '$ys'],
           [case, ['decons-atom', '$xs'],
            [[['$head', '$tail'],
              [let, '$__tr_append_rest',
               [append, '$tail', '$ys'],
               ['cons-atom', '$head', '$__tr_append_rest']]]]]])
]).

petta_lib_petta_import_items([
    exec(['import!', '&self', lib_petta])
]).

petta_lib_petta_inline_items(HelperKeys, Items) :-
    pe_petta_lib_petta_helper_decls(HelperKeys, Decls),
    wrap_plain_items(Decls, Items).

wrap_plain_item(Decl, plain(Decl)).

wrap_plain_items(Decls, Items) :-
    maplist(wrap_plain_item, Decls, Items).

petta_length_compat_items(Direction, [
    plain(['=', [length, '$expr'],
           [let, '$tuple', [eval, '$expr'], ['size-atom', '$tuple']]])
]) :-
    petta_he_profile_direction(Direction), !.
petta_length_compat_items(_, [
    plain(['=', [length, '$expr'],
           ['size-atom', '$expr']])
]).

petta_quote_compat_items([
    plain(['=', [QuoteFun, [quote, '$expr']], '$expr'])
]) :-
    pe_quoted_syntax_fun(QuoteFun).

petta_state_compat_items(Items) :-
    pe_petta_state_clear_fun(ClearFun),
    pe_petta_state_set_fun(SetFun),
    pe_petta_state_get_fun(GetFun),
    pe_petta_state_cell_fun(CellFun),
    Items = [
    plain(['=', [ClearFun, '$name'],
           [let, '$__tr_state_removed',
            [collapse,
             [match, '&self', [CellFun, '$name', '$old'],
              ['remove-atom', '&self',
               [CellFun, '$name', '$old']]]],
            'True']]),
    plain(['=', [SetFun, '$name', '$value'],
           [let, '$__tr_state_cleared',
            [ClearFun, '$name'],
            [let, '$__tr_state_added',
             ['add-atom', '&self',
              [CellFun, '$name', '$value']],
             'True']]]),
    plain(['=', [GetFun, '$name'],
           [match, '&self', [CellFun, '$name', '$value'],
            '$value']])
    ].

rewrite_builtin_test_item(exec(Expr), exec(TExpr)) :-
    rewrite_builtin_test_term(Expr, TExpr).
rewrite_builtin_test_item(plain(Expr), plain(TExpr)) :-
    rewrite_builtin_test_term(Expr, TExpr).

rewrite_builtin_test_term([test, Actual, Expected],
                          Rewritten) :-
    !,
    rewrite_builtin_test_term(Actual, RActual),
    rewrite_builtin_test_term(Expected, RExpected),
    (   petta_to_he:alpha_runtime_bool_test_actual(RActual, Expected),
        petta_to_he:lift_alpha_runtime_bool_actual(RActual, Binder, Value)
    ->  pe_petta_test_runtime_bool_fun(TestFun),
        Rewritten = [let, Binder, Value, [TestFun, Binder, RExpected]]
    ;   builtin_test_helper_head(Actual, Expected, TestFun),
        Rewritten = [TestFun, RActual, RExpected]
    ).
rewrite_builtin_test_term(List, Rewritten) :-
    is_list(List), !,
    maplist(rewrite_builtin_test_term, List, Rewritten).
rewrite_builtin_test_term(Term, Term).

builtin_test_helper_head(Actual, _Expected, 'petta-test-bag-equal') :-
    pe_test_call_needs_bag_equality(Actual),
    !.
builtin_test_helper_head(Actual, Expected, 'petta-test-runtime-bool') :-
    petta_to_he:alpha_runtime_bool_test_actual(Actual, Expected),
    !.
builtin_test_helper_head(Actual, Expected, 'petta-test-results-data') :-
    pe_test_call_needs_collapse(Actual),
    test_expected_literal_data(Expected),
    !.
builtin_test_helper_head(Actual, _Expected, 'petta-test-results') :-
    pe_test_call_needs_collapse(Actual),
    !.
builtin_test_helper_head(_Actual, Expected, 'petta-test-equal-data') :-
    test_expected_literal_data(Expected),
    !.
builtin_test_helper_head(_, _, 'petta-test-equal').

test_expected_literal_data([quote, _]) :-
    !.
test_expected_literal_data(Term) :-
    atom(Term),
    \+ petta_to_he:callable_arity(Term, 0),
    !.
test_expected_literal_data(Term) :-
    \+ is_list(Term),
    !.
test_expected_literal_data([Head|_]) :-
    is_list(Head),
    !.
test_expected_literal_data([Head|_]) :-
    atom(Head),
    \+ petta_to_he:source_variable_atom(Head),
    \+ petta_to_he:callable_arity(Head, _),
    \+ test_expected_eval_head(Head).

test_expected_eval_head(progn).
test_expected_eval_head(prog1).
test_expected_eval_head(if).
test_expected_eval_head(case).
test_expected_eval_head(let).
test_expected_eval_head('let*').
test_expected_eval_head(chain).

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
    Spec = [library, Payload],
    atom(Payload),
    file_directory_name(SourcePath, SourceDir),
    resolve_library_module_file(SourceDir, Payload, Resolved),
    Style = bare, !.
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

resolve_library_module_file(SourceDir, Payload, Resolved) :-
    module_file_candidate(Payload, Candidate),
    ancestor_dir(SourceDir, AncestorDir),
    directory_file_path(AncestorDir, lib, LibDir),
    directory_file_path(LibDir, Candidate, Resolved0),
    exists_file(Resolved0),
    atom_concat(_, '.metta', Resolved0),
    Resolved = Resolved0,
    !.

ancestor_dir(Dir, Dir).
ancestor_dir(Dir, Ancestor) :-
    file_directory_name(Dir, Parent),
    Parent \== Dir,
    ancestor_dir(Parent, Ancestor).

spec_payload(Spec, Payload, quoted) :-
    atom(Spec),
    atom_chars(Spec, ['"'|Rest]),
    append(Mid, ['"'], Rest),
    atom_chars(Payload, Mid), !.
spec_payload(Spec, Spec, bare) :-
    atom(Spec).

relativize_spec_for_output(OutputPath, Resolved, Style, TSpec) :-
    file_directory_name(OutputPath, OutputDir),
    directory_as_base(OutputDir, OutputBase),
    relative_file_name(Resolved, OutputBase, Rel),
    rebuild_spec(Rel, Style, TSpec).

directory_as_base(Dir, Dir) :-
    sub_atom(Dir, _, 1, 0, /), !.
directory_as_base(Dir, Base) :-
    atom_concat(Dir, '/', Base).

rebuild_spec(Payload, bare, Payload).
rebuild_spec(Payload, quoted, Spec) :-
    atomic_list_concat(['"', Payload, '"'], Spec).

translate_file_tree_inplace_recursive(_, SourcePath, _, Seen, Seen) :-
    memberchk(pair(SourcePath, _), Seen), !.
translate_file_tree_inplace_recursive(Direction, SourcePath, OutSuffix,
                                      SeenIn, SeenOut) :-
    translated_sibling_path(SourcePath, OutSuffix, OutPath),
    read_metta_file(SourcePath, Atoms0),
    maybe_rewrite_he_source_import_snapshots(Direction, SourcePath, Atoms0, Atoms),
    length(Atoms, N),
    translate_toplevel_atoms(Direction, Atoms, TAtoms0),
    rewrite_inplace_recursive_module_surfaces(SourcePath, OutPath, OutSuffix,
        TAtoms0, TAtoms1, Deps),
    maybe_inline_he_entry_helpers(Direction, SeenIn, TAtoms1, TAtoms),
    setup_call_cleanup(
        open(OutPath, write, Stream),
        (
            write_translation_header(Stream, Direction, SourcePath, N),
            format(Stream, "; Mode: recursive~n~n", []),
            forall(member(TA, TAtoms), write_toplevel_atom(Stream, TA)),
            maybe_materialize_petta_helper_libs(TAtoms, OutPath)
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
    read_metta_file(SourcePath, Atoms0),
    maybe_rewrite_he_source_import_snapshots(Direction, SourcePath, Atoms0, Atoms),
    length(Atoms, N),
    translate_toplevel_atoms(Direction, Atoms, TAtoms0),
    rewrite_recursive_module_surfaces(SourceRootDir, OutputRootDir, SourcePath,
        OutPath, TAtoms0, TAtoms1, Deps),
    maybe_inline_he_entry_helpers(Direction, SeenIn, TAtoms1, TAtoms),
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
            forall(member(TA, TAtoms), write_toplevel_atom(Stream, TA)),
            maybe_materialize_petta_helper_libs(TAtoms, OutPath)
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

maybe_rewrite_he_source_import_snapshots(Direction, SourcePath, Atoms0, Atoms) :-
    (   he2petta_direction_name(Direction)
    ->  rewrite_he_source_import_snapshots(SourcePath, Atoms0, Atoms)
    ;   Atoms = Atoms0
    ).

rewrite_he_source_import_snapshots(SourcePath, Atoms0, Atoms) :-
    rewrite_he_source_import_snapshots_acc(SourcePath, Atoms0, [], Atoms).

rewrite_he_source_import_snapshots_acc(_, [], _, []).
rewrite_he_source_import_snapshots_acc(SourcePath, ['!', ['import!', SpaceRef, Spec]|Rest],
                                       ImportedRefs, ['!', Rewritten|OutRest]) :-
    atom(SpaceRef),
    SpaceRef \== '&self',
    resolve_local_module_file(SourcePath, Spec, ResolvedFile, _Style),
    he_snapshot_export_atoms(ResolvedFile, DirectAtoms),
    !,
    he_snapshot_import_expr(SpaceRef, DirectAtoms, Rewritten),
    sort([SpaceRef|ImportedRefs], ImportedRefs1),
    rewrite_he_source_import_snapshots_acc(SourcePath, Rest, ImportedRefs1, OutRest).
rewrite_he_source_import_snapshots_acc(SourcePath, [Atom0|Rest], ImportedRefs, [Atom|OutRest]) :-
    rewrite_imported_space_get_type(ImportedRefs, Atom0, Atom),
    rewrite_he_source_import_snapshots_acc(SourcePath, Rest, ImportedRefs, OutRest).

he_snapshot_export_atoms(SourcePath, DirectAtoms) :-
    read_metta_file(SourcePath, Atoms),
    he_snapshot_visible_atoms(Atoms, Visible0),
    he_snapshot_reorder_visible_atoms(Visible0, DirectAtoms).

he_snapshot_visible_atoms([], []).
he_snapshot_visible_atoms(['!', _ExecExpr|Rest], Visible) :-
    !,
    he_snapshot_visible_atoms(Rest, Visible).
he_snapshot_visible_atoms(['!'|Rest], Visible) :-
    !,
    he_snapshot_visible_atoms(Rest, Visible).
he_snapshot_visible_atoms([Atom|Rest], [Atom|Visible]) :-
    he_snapshot_visible_atoms(Rest, Visible).

he_snapshot_reorder_visible_atoms(Visible0, Ordered) :-
    partition(he_snapshot_type_decl_atom, Visible0, TypeDecls, OtherAtoms),
    append(OtherAtoms, TypeDecls, Ordered).

he_snapshot_type_decl_atom([':', _, _]).

he_snapshot_import_expr(SpaceRef, DirectAtoms, Expr) :-
    he_snapshot_add_bindings(SpaceRef, DirectAtoms, 1, Bindings),
    Expr = ['let*', Bindings, '()'].

he_snapshot_add_bindings(_, [], _, []).
he_snapshot_add_bindings(SpaceRef, [Atom|Rest], N, [[Var, ['add-atom', SpaceRef, Atom]]|Bindings]) :-
    format(atom(Var), '$__tr_import_~d', [N]),
    N1 is N + 1,
    he_snapshot_add_bindings(SpaceRef, Rest, N1, Bindings).

rewrite_imported_space_get_type(ImportedRefs, ['get-type', Ref], [quote, 'SpaceType']) :-
    atom(Ref),
    memberchk(Ref, ImportedRefs),
    !.
rewrite_imported_space_get_type(_, [quote|Payload], [quote|Payload]) :- !.
rewrite_imported_space_get_type(ImportedRefs, List0, List) :-
    is_list(List0),
    !,
    maplist(rewrite_imported_space_get_type(ImportedRefs), List0, List).
rewrite_imported_space_get_type(_, Atom, Atom).

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
    setup_path_compat_fixture,
    format("~n=== File Translation Path Compatibility Tests ===~n"),
    forall(path_compat_case(N, Name, Goal), run_path_compat_case(N, Name, Goal)),
    verify_behavior_contract_coverage,
    format("~n=== File Translation Behavior Contract Tests ===~n"),
    forall(path_behavior_case(Contract, Name, Goal),
           run_path_behavior_case(Contract, Name, Goal)).

run_path_compat_case(N, Name, Goal) :-
    (   call(Goal)
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n", [N, Name]),
        fail
    ).

run_path_behavior_case(Contract, Name, Goal) :-
    (   call(Goal)
    ->  format("  ✓ ~w: ~w~n", [Contract, Name])
    ;   format("  ✗ ~w: ~w~n", [Contract, Name]),
        fail
    ).

verify_behavior_contract_coverage :-
    forall(behavior_contract(Contract, _),
           (   path_behavior_case(Contract, _, _)
           ->  true
           ;   format("  ✗ policy: missing executable behavior case for contract ~w~n",
                      [Contract]),
               fail
           )).

path_compat_case(1, "plain local import spec rewrites relative to translated output",
    (   path_fixture('test_import_nested_depth.metta', Source),
        path_generated('out/test_import_nested_depth.petta.metta', Output),
        relocate_local_import_spec(Source, Output,
            'support/import_deep/root.metta',
            '../source_fixture/support/import_deep/root.metta')
    )).

path_compat_case(2, "bare helper import resolves to local .metta file",
    (   path_fixture('support/import_pkg/moduleA.metta', Source),
        path_generated('out/moduleA.he.metta', Output),
        relocate_local_import_spec(Source, Output,
            'Helper',
            '../source_fixture/support/import_pkg/Helper.metta')
    )).

path_compat_case(3, "register-module! root relocates relative to translated output",
    (   path_fixture('test_import_modules.metta', Source),
        path_generated('out/test_import_modules.petta.metta', Output),
        relocate_local_module_root(Source, Output,
            'support/import_pkg',
            '../source_fixture/support/import_pkg')
    )).

path_compat_case(4, "foreign/python import surface is intentionally untouched",
    (   path_fixture('test_import_foreign_python_file.metta', Source),
        path_generated('out/test_import_foreign_python_file.he.metta', Output),
        relocate_local_import_spec(Source, Output,
            'support/import_foreign_pyfile',
            'support/import_foreign_pyfile')
    )).

path_compat_case(5, "recursive translation keeps files in place with renamed outputs",
    (   path_generated('inplace_fixture', FixtureRoot),
        setup_recursive_fixture(FixtureRoot),
        directory_file_path(FixtureRoot, 'test_import_modules.metta', Entry),
        directory_file_path(FixtureRoot, 'test_import_modules.he2petta.metta', EntryOut),
        directory_file_path(FixtureRoot, 'support/import_pkg/moduleA.he2petta.metta', ModuleOut),
        translate_file_he_to_petta_recursive(
            Entry, '.he2petta.metta'),
        file_contains_text(EntryOut,
            "!(register-module! support/import_pkg)"),
        % import! is unit-wrapped (HE returns ()), so match the call shape
        % rather than a leading bang.
        file_contains_text(EntryOut,
            "(import! &db support/import_pkg/moduleA.he2petta.metta)"),
        exists_file(ModuleOut),
        file_contains_text(ModuleOut,
            "(import! &self Helper.he2petta.metta)")
    )).

path_compat_case(6, "bundle translation emits manifest and bundled entry file",
    (   path_generated('bundle_he', BundleDir),
        path_fixture('test_import_nested_depth.metta', Entry),
        directory_file_path(BundleDir, 'bundle_manifest.tsv', Manifest),
        directory_file_path(BundleDir, 'test_import_nested_depth.metta', EntryOut),
        directory_file_path(BundleDir, 'support/import_deep/root.metta', RootOut),
        translate_file_he_to_petta_bundle(Entry, BundleDir),
        exists_file(Manifest),
        file_contains_text(EntryOut,
            "(add-atom &deep (deep-root loaded))"),
        \+ exists_file(RootOut)
    )).

path_compat_case(6_1, "HE->PeTTa file translation renames callable equality heads without breaking declaration syntax",
    (   path_fixture('test_he_eq_surface.metta', Source),
        path_generated('out/test_he_eq_surface.petta.metta', Output),
        translate_file_he_to_petta(Source, Output),
        file_contains_text(Output, "(= (=-he $x $x) T)"),
        file_contains_text(Output, "(call-or-inert (quote (=-he Socrates Socrates)))"),
        \+ file_contains_text(Output, "(= (= $x $x) T)")
    )).

path_compat_case(6_2, "HE->PeTTa file translation preserves pre-definition reserved head spelling",
    (   path_fixture('test_he_reserved_head_order_surface.metta', Source),
        path_generated('out/test_he_reserved_head_order_surface.petta.metta', Output),
        translate_file_he_to_petta(Source, Output),
        file_contains_text(Output, "!(let $x (match-template-eval foo) (quote (is-space $x)))"),
        file_contains_text(Output, "(: is-space-he (-> Atom Bool))"),
        file_contains_text(Output, "(= (is-space-he $atom) T)"),
        file_contains_text(Output, "(source-defined-function is-space)")
    )).

path_compat_case(6_3, "HE->PeTTa file translation rejects doc-surface portability gaps explicitly",
    (   path_fixture('test_he_doc_surface.metta', Source),
        path_generated('out/test_he_doc_surface.petta.metta', Output),
        catch((translate_file_he_to_petta(Source, Output), Outcome = translated),
              error(domain_error(he_core_surface, doc_surface), context(_, Message)),
              Outcome = rejected(Message)),
        Outcome = rejected(Message),
        sub_string(Message, _, _, _, 'no portable doc-surface translation')
    )).

path_compat_case(7, "default PeTTa->HE file translation lowers hyperpose and keeps once pure",
    (   path_fixture('test_hyperpose_surface.metta', Source),
        path_generated('out/test_hyperpose_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "collapse (superpose ((slow-branch) (cheap-branch)))"),
        file_contains_text(Output, "decons-atom"),
        \+ file_contains_text(Output, "select")
    )).

path_compat_case(8, "hyperpose-preserving PeTTa->HE file translation keeps hyperpose and pure once",
    (   path_fixture('test_hyperpose_surface.metta', Source),
        path_generated('out/test_hyperpose_surface.hyperpose.he.metta', Output),
        translate_file_petta_to_he_hyperpose(Source, Output),
        file_contains_text(Output, "collapse (hyperpose ((slow-branch) (cheap-branch)))"),
        file_contains_text(Output, "decons-atom"),
        \+ file_contains_text(Output, "select")
    )).

path_compat_case(9, "PeTTa->HE file translation inlines test helpers instead of importing lib_petta",
    (   path_fixture('test_hyperpose_surface.metta', Source),
        path_generated('out/test_hyperpose_surface.with_test.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "petta-test-"),
        file_contains_text(Output, "(= (petta-public-term $expr)"),
        \+ file_contains_text(Output, "(: test (-> Atom Atom Bool))")
    )).

path_compat_case(10, "default PeTTa->HE file translation lowers canonical single-match cut idiom",
    (   path_fixture('test_cut_surface.metta', Source),
        path_generated('out/test_cut_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "(cut)"),
        file_contains_text(Output, "(collapse (match $space $pat $ret))"),
        file_contains_text(Output, "decons-atom")
    )).

path_compat_case(11, "default PeTTa->HE file translation still rejects raw cut",
    (   path_fixture('test_raw_cut_surface.metta', Source),
        path_generated('out/test_raw_cut_surface.he.metta', Output),
        catch((translate_file_petta_to_he(Source, Output), Outcome = translated),
              error(domain_error(he_core_surface, cut), _),
              Outcome = rejected),
        Outcome == rejected
    )).

path_compat_case(12, "PeTTa-profile file translation preserves cut",
    (   path_fixture('test_cut_surface.metta', Source),
        path_generated('out/test_cut_surface.petta-he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(cut)")
    )).

path_compat_case(13, "default PeTTa->HE file translation inlines assertion-only msort bag helpers",
    (   path_fixture('test_msort_surface.metta', Source),
        path_generated('out/test_msort_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "petta-test-bag-equal"),
        file_contains_text(Output, "(= (petta-test-bag-equal $actual $expected)")
    )).

path_compat_case(14, "PeTTa-profile file translation preserves native msort",
    (   path_fixture('test_msort_surface.metta', Source),
        path_generated('out/test_msort_surface.petta-he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(msort (collapse")
    )).

path_compat_case(15, "default PeTTa->HE length helper uses upstream-safe size-atom",
    (   path_fixture('test_length_surface.metta', Source),
        path_generated('out/test_length_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (length $expr) (size-atom $expr))"),
        \+ file_contains_text(Output, "(eval $expr)")
    )).

path_compat_case(16, "PeTTa-profile length helper uses profile eval fast path",
    (   path_fixture('test_length_surface.metta', Source),
        path_generated('out/test_length_surface.petta-he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))")
    )).

path_compat_case(17, "PeTTa->HE file translation emits local lib_petta for second-from-pair",
    (   path_fixture('test_second_from_pair_surface.metta', Source),
        path_generated('out/test_second_from_pair_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (second-from-pair $pair)")
    )).

path_compat_case(18, "user-defined second-from-pair does not pull lib_petta",
    (   path_fixture('test_second_from_pair_user_surface.metta', Source),
        path_generated('out/test_second_from_pair_user_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "lib_petta")
    )).

path_compat_case(18_1, "default PeTTa->HE file translation emits local lib_petta for reverse",
    (   path_fixture('test_reverse_surface.metta', Source),
        path_generated('out/test_reverse_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (reverse $xs)")
    )).

path_compat_case(18_2, "default PeTTa->HE file translation emits local lib_petta for last",
    (   path_fixture('test_last_surface.metta', Source),
        path_generated('out/test_last_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (last $xs)")
    )).

path_compat_case(18_3, "default PeTTa->HE file translation emits local lib_petta for short foldl",
    (   path_fixture('test_foldl_surface.metta', Source),
        path_generated('out/test_foldl_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (foldl $f $list $init)")
    )).

path_compat_case(18_4, "default PeTTa->HE file translation emits local lib_petta for alpha-unique-atom",
    (   path_fixture('test_alpha_unique_atom_surface.metta', Source),
        path_generated('out/test_alpha_unique_atom_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (alpha-unique-atom $tuple)")
    )).

path_compat_case(18_5, "default PeTTa->HE file translation emits local lib_petta for min/max",
    (   path_fixture('test_minmax_surface.metta', Source),
        path_generated('out/test_minmax_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (min $a $b)"),
        file_contains_text(HelperOut, "(= (max $a $b)")
    )).

path_compat_case(18_6, "alpha helper-backed tests use the runtime-bool helper",
    (   path_fixture('test_alpha_equal_surface.metta', Source),
        path_generated('out/test_alpha_equal_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(let $__tr_alpha_equal_eval_"),
        file_contains_text(Output, "(petta-test-runtime-bool $__tr_alpha_equal_eval_"),
        \+ file_contains_text(Output, "!(petta-test-results-data (let $__tr_alpha_equal_eval_"),
        \+ file_contains_text(Output, "!(petta-test-equal-data (let $__tr_alpha_equal_eval_")
    )).

path_compat_case(18_7, "default PeTTa->HE preserves raw nested syntax inside data tuples while inlining closed concrete runtime surfaces",
    (   path_fixture('test_runtime_surface_raw_tuple.metta', Source),
        path_generated('out/test_runtime_surface_raw_tuple.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(within (quote (fib 5)))"),
        file_contains_text(Output, "(call-within (let $__tr_runtime_call_"),
        file_contains_text(Output, "(unquote (quote (fib 5)))"),
        file_contains_text(Output, "(quote-within (quote (fib 5)))"),
        file_contains_text(Output, "(eval-within (let $__tr_runtime_eval_"),
        file_contains_text(Output, "(reduce-within (let $__tr_runtime_reduce_"),
        \+ file_contains_text(Output, "(within (fib 5))")
    )).

path_compat_case(19, "mixed test surfaces route per call and inline the needed helpers",
    (   path_fixture('test_mixed_test_surface.metta', Source),
        path_generated('out/test_mixed_test_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "!(petta-test-equal-data (+ 1 2) 3)"),
        file_contains_text(Output, "!(petta-test-results-data (if $x yes no) (yes no))"),
        file_contains_text(Output, "(= (petta-public-term $expr)")
    )).

path_compat_case(20, "PeTTa->HE file translation materializes local imported modules as sidecar deps",
    (   path_fixture('test_local_import_materialization.metta', Source),
        path_generated('out/test_local_import_materialization.he.metta', Output),
        path_generated('out/petta_dep_support_local_dep_lib.metta', DepOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self petta_dep_support_local_dep_lib)"),
        exists_file(DepOut),
        file_contains_text(DepOut, "(= (dep-f $x) (+ $x 1))")
    )).

path_compat_case(21, "PeTTa->HE file translation materializes library imports as sidecar deps",
    (   path_fixture('test_library_import_materialization.metta', Source),
        path_generated('out/test_library_import_materialization.he.metta', Output),
        path_generated('out/petta_dep_lib_lib_roman.metta', DepOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self petta_dep_lib_lib_roman)"),
        exists_file(DepOut),
        file_contains_text(DepOut, "(= (map-flat $f $list) (map-atom $list $item (petta-apply1 $f $item)))"),
        file_contains_text(DepOut, "(= (/==\\ $a $b) (let $intersection (intersection-atom $a $b) $intersection))"),
        file_contains_text(DepOut, "(= (\\== $a $b) (let $difference (subtraction-atom $a $b) $difference))"),
        file_contains_text(DepOut, "(= (\\==/ $a $b) (let $difference (subtraction-atom $a $b) (union-atom $difference $b)))")
    )).

path_compat_case(22, "PeTTa->HE bundle translation rewrites library imports to bundled files",
    (   path_generated('bundle_petta_library', BundleDir),
        path_fixture('test_library_import_materialization.metta', Entry),
        directory_file_path(BundleDir, 'test_library_import_materialization.metta', EntryOut),
        directory_file_path(BundleDir, 'lib/lib_roman.metta', DepOut),
        translate_file_petta_to_he_bundle(Entry, BundleDir),
        file_contains_text(EntryOut, "!(import! &self lib/lib_roman.metta)"),
        exists_file(DepOut)
    )).

path_compat_case(23, "PeTTa->HE file translation reports pure-unsupported imported dependency precisely",
    (   path_fixture('test_imported_dependency_blocker.metta', Source),
        path_generated('out/test_imported_dependency_blocker.he.metta', Output),
        catch((translate_file_petta_to_he(Source, Output), Outcome = translated),
              error(domain_error(he_core_surface, msort), context(_, Message)),
              Outcome = rejected(Message)),
        Outcome = rejected(Message),
        sub_string(Message, _, _, _, "support/imported_blocker.metta"),
        sub_string(Message, _, _, _, "test_imported_dependency_blocker.metta")
    )).

path_compat_case(24, "PeTTa->HE file translation rewrites builtin partials to inline local helpers",
    (   path_fixture('test_partial_builtin_surface.metta', Source),
        path_generated('out/partial_builtin/test_partial_builtin_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "(: petta-lambda (-> Atom $t (-> $a $t)))"),
        file_contains_text(Output, "(: petta-apply1 (-> Atom Atom Atom))"),
        file_contains_text(Output, "(= (petta-partial-1 $__tr_"),
        file_contains_text(Output, "(= (inc) petta-partial-1)"),
        file_contains_text(Output, "!(petta-apply1 (inc) 2)")
    )).

path_compat_case(25, "generated builtin partial helper names avoid source collisions with inline helpers",
    (   path_fixture('test_partial_builtin_helper_collision.metta', Source),
        path_generated('out/partial_builtin_collision/test_partial_builtin_helper_collision.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "(: petta-lambda (-> Atom $t (-> $a $t)))"),
        file_contains_text(Output, "(: petta-apply1 (-> Atom Atom Atom))"),
        file_contains_text(Output, "(= (petta-partial-1 $x) user-defined)"),
        file_contains_text(Output, "(= (petta-partial-2 $__tr_"),
        file_contains_text(Output, "(= (inc) petta-partial-2)"),
        file_contains_text(Output, "!(petta-apply1 (inc) 2)")
    )).

path_compat_case(26, "default PeTTa->HE file translation still rejects raw standalone msort",
    (   path_fixture('test_raw_msort_surface.metta', Source),
        path_generated('out/test_raw_msort_surface.he.metta', Output),
        catch((translate_file_petta_to_he(Source, Output), Outcome = translated),
              error(domain_error(he_core_surface, msort), _),
              Outcome = rejected),
        Outcome == rejected
    )).

path_compat_case(27, "Expression-typed callable-data family rewrites calls through quote and decons-atom",
    (   path_fixture('test_exprdata_callable_surface.metta', Source),
        path_generated('out/test_exprdata_callable_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (map-flat3 $pairq) (let ($head $tail) (decons-atom $pairq)"),
        file_contains_text(Output, "(= (map-flat4 $pairq) (let ($head $tail) (decons-atom $pairq)"),
        file_contains_text(Output, "!(petta-test-results-data (map-flat3 (quote (p1 (1 2)))) (2 3))"),
        file_contains_text(Output, "!(petta-test-results-data (map-flat4 (quote (x (p1 (1 2))))) (2 3))")
    )).

path_compat_case(28, "Closed unary callable composition rewrites to a reusable helper symbol",
    (   path_fixture('test_partial_composition_surface.metta', Source),
        path_generated('out/test_partial_composition_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (petta-partial-1 $__tr_"),
        file_contains_text(Output, "(= (petta-partial-2 $__tr_"),
        file_contains_text(Output, "(= (petta-partial-3 $__tr_"),
        file_contains_text(Output, "(= (.. $f1 $f2 $arg) (petta-apply1 $f1 ($f2 $arg)))"),
        file_contains_text(Output, "(= (plus1times2) petta-partial-3)"),
        file_contains_text(Output, "!(petta-test-equal-data (petta-apply1 (plus1times2) 1) 4)")
    )).

path_compat_case(29, "finite generator function heads lower through superpose guards and bag-equality tests",
    (   path_fixture('test_functionhead_guard_surface.metta', Source),
        path_generated('out/test_functionhead_guard_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (myplus $__tr_head_arg_"),
        file_contains_text(Output, "(let $__tr_head_candidate_"),
        file_contains_text(Output, "(superpose (1 2 3))"),
        file_contains_text(Output, "(superpose (2 3))"),
        file_contains_text(Output, "(unify $__tr_head_candidate_"),
        file_contains_text(Output, "(let $__tr_member_value_"),
        file_contains_text(Output, "!(petta-test-bag-equal (myplus $x $y) (3 4 4 5 5))"),
        file_contains_text(HelperOut, "(= (is-member $item $tuple)")
    )).

path_compat_case(30, "duplicate head variables become explicit unify guards in file translation",
    (   path_fixture('test_functionhead_duplicate_surface.metta', Source),
        path_generated('out/test_functionhead_duplicate_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (same $x $__tr_head_arg_"),
        file_contains_text(Output, "(unify $__tr_head_arg_"),
        file_contains_text(Output, " ok Empty)")
    )).

path_compat_case(31, "append-suffix function heads lower through structural decons in file translation",
    (   path_fixture('test_functionhead_append_suffix_surface.metta', Source),
        path_generated('out/test_functionhead_append_suffix_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (h $__tr_head_arg_"),
        file_contains_text(Output, "(chain (decons-atom $__tr_head_arg_"),
        file_contains_text(Output, "(first-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(second-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(unify $__tr_head_elem_"),
        file_contains_text(Output, "(let $__tr_head_suffix_"),
        file_contains_text(Output, "(eval (atom-subst $__tr_head_suffix_"),
        file_contains_text(Output, "$__tr_apply_fun_"),
        file_contains_text(Output, "$C))")
    )).

path_compat_case(32, "equality-form function-call inversion normalizes into the same structural file surface",
    (   path_fixture('test_functionhead_eq_guard_surface.metta', Source),
        path_generated('out/test_functionhead_eq_guard_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (h_unify $__tr_head_arg_"),
        file_contains_text(Output, "(chain (decons-atom $__tr_head_arg_"),
        file_contains_text(Output, "(first-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(second-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(unify $__tr_head_elem_"),
        file_contains_text(Output, "(let $__tr_head_suffix_"),
        file_contains_text(Output, "(eval (atom-subst $__tr_head_suffix_"),
        file_contains_text(Output, "$__tr_apply_fun_"),
        file_contains_text(Output, "$C))")
    )).

path_compat_case(33, "pure structural function-call inversion let-patterns lower through decons",
    (   path_fixture('test_function_call_inversion_structural_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_structural_let_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (probe) (chain (decons-atom (1 2 3 4))"),
        file_contains_text(Output, "(first-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(second-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(eval (atom-subst $Head $__tr_apply_fun_"),
        file_contains_text(Output, "$Tail)))"),
        \+ file_contains_text(Output, "(let (f $Head $Tail) (1 2 3 4)")
    )).

path_compat_case(34, "pure arithmetic function-call inversion let-patterns reject instead of miscompiling",
    (   path_fixture('test_function_call_inversion_arith_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_arith_let_surface.he.metta', Output),
        catch((translate_file_petta_to_he(Source, Output), Outcome = translated),
              error(domain_error(he_core_surface, arithmetic_inversion), _),
              Outcome = rejected),
        Outcome == rejected
    )).

path_compat_case(35, "PeTTa-profile arithmetic function-call inversion let-patterns keep raw data-headed application shape",
    (   path_fixture('test_function_call_inversion_arith_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_arith_let_surface.petta_he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(= (probe) (let (g $X $Y 35) (42 2 3)"),
        file_contains_text(Output, "(eval (atom-subst $X $__tr_apply_fun_"),
        file_contains_text(Output, "$Y 40)))"),
        \+ file_contains_text(Output, "(petta-apply2 $X $Y 40)")
    )).

path_compat_case(36, "ffi-tokens mode lowers arithmetic function-call inversion to explicit ffi surface",
    (   path_fixture('test_function_call_inversion_arith_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_arith_let_surface.ffi_tokens.metta', Output),
        translate_file_petta_to_he_ffi_tokens(Source, Output),
        file_contains_text(Output, "(= (probe) (petta-ffi-function-call-inversion arithmetic-append-suffix"),
        file_contains_text(Output, "(quote (g $X $Y 35))"),
        file_contains_text(Output, "(eval (atom-subst $X $__tr_apply_fun_"),
        file_contains_text(Output, "$Y 40)))"),
        \+ file_contains_text(Output, "domain_error(he_core_surface")
    )).

path_compat_case(37, "PeTTa-profile file translation preserves native test surface",
    (   path_fixture('test_profile_native_test_surface.metta', Source),
        path_generated('out/test_profile_native_test_surface.petta_he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "!(test (wu1 (+ 2 4) (+ 4 2)) (quote (42 6 (+ 4 2))))"),
        \+ file_contains_text(Output, "petta-test-equal"),
        \+ file_contains_text(Output, "petta-test-results")
    )).

path_compat_case(38, "PeTTa-profile file translation preserves native eval/call/reduce surfaces",
    (   path_fixture('test_profile_eval_surface.metta', Source),
        path_generated('out/test_profile_eval_surface.petta_he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(eval $fbody_specialized)"),
        file_contains_text(Output, "($res (reduce (myfunc)))"),
        \+ file_contains_text(Output, "(unquote $fbody_specialized)"),
        \+ file_contains_text(Output, "(unquote (quote (myfunc)))")
    )).

path_compat_case(39, "PeTTa-profile file translation preserves member-filter source calls in generator bodies",
    (   path_fixture('test_functionhead_guard_surface.metta', Source),
        path_generated('out/test_functionhead_guard_surface.petta_he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(= (myplus (in $X (1 2 3)) (in $Y (2 3))) (in (+ $X $Y) (3 4 5)))"),
        \+ file_contains_text(Output, "(let $__tr_member_value_")
    )).

path_compat_case(40, "PeTTa-profile file translation preserves expression-data recursive call arguments",
    (   path_fixture('test_exprdata_callable_surface.metta', Source),
        path_generated('out/test_exprdata_callable_surface.petta_he.metta', Output),
        translate_file_petta_to_he_petta_he(Source, Output),
        file_contains_text(Output, "(= (map-flat3 ($f (cons $x $xs))) (cons ($f $x) (map-flat3 ($f $xs))))"),
        file_contains_text(Output, "(= (map-flat4 ($v ($f (cons $x $xs)))) (cons ($f $x) (map-flat4 ($v ($f $xs)))))"),
        \+ file_contains_text(Output, "(quote (p1 (1 2)))"),
        \+ file_contains_text(Output, "(quote ($f $xs))")
    )).

path_behavior_case(variable_head_data_callable_boundary,
    "pure file translation preserves data-tuple and callable-lambda variable-head runtime behavior",
    (   path_fixture('test_variable_head_boundary_behavior.metta', Source),
        path_generated('out/test_variable_head_boundary_behavior.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        run_petta_runtime(default, Source, SourceRc, SourceOut, _SourceErr),
        run_petta_runtime(he, Output, HeRc, HeOut, _HeErr),
        SourceRc =:= 0,
        HeRc =:= 0,
        \+ sub_string(SourceOut, _, _, _, "❌"),
        \+ sub_string(HeOut, _, _, _, "❌"),
        normalize_runtime_output(SourceOut, Normalized),
        normalize_runtime_output(HeOut, Normalized)
    )).

file_contains_text(Path, Snippet) :-
    read_file_to_string(Path, Text, []),
    sub_string(Text, _, _, _, Snippet).

petta_profile_run_sh(Path) :-
    source_file(run_path_compat_tests, SourceFile),
    file_directory_name(SourceFile, SourceDir),
    directory_file_path(SourceDir, '../petta-he-profile/run.sh', RelPath),
    absolute_file_name(RelPath, Path, [solutions(first)]).

runtime_timeout_seconds('30').

run_petta_runtime(default, File, Rc, Stdout, Stderr) :-
    petta_profile_run_sh(RunSh),
    runtime_timeout_seconds(Timeout),
    process_create(path(timeout), ['--kill-after=5', Timeout, RunSh, File, '--silent'],
                   [stdout(pipe(OutPipe)),
                    stderr(pipe(ErrPipe)),
                    process(Pid)]),
    read_string(OutPipe, _, Stdout),
    close(OutPipe),
    read_string(ErrPipe, _, Stderr),
    close(ErrPipe),
    process_wait(Pid, exit(Rc)).
run_petta_runtime(he, File, Rc, Stdout, Stderr) :-
    petta_profile_run_sh(RunSh),
    runtime_timeout_seconds(Timeout),
    process_create(path(timeout), ['--kill-after=5', Timeout, RunSh, '--he', File, '--silent'],
                   [stdout(pipe(OutPipe)),
                    stderr(pipe(ErrPipe)),
                    process(Pid)]),
    read_string(OutPipe, _, Stdout),
    close(OutPipe),
    read_string(ErrPipe, _, Stderr),
    close(ErrPipe),
    process_wait(Pid, exit(Rc)).

normalize_runtime_output(Text, Normalized) :-
    split_string(Text, "\n", "\r \t", Lines0),
    exclude(runtime_noise_line, Lines0, Lines1),
    exclude(string_empty, Lines1, Lines),
    include(assertion_surface_line, Lines, AssertionLines),
    (   AssertionLines = []
    ->  atomics_to_string(Lines, "\n", Normalized)
    ;   maplist(assertion_surface_status, AssertionLines, Statuses),
        atomics_to_string(Statuses, "\n", Normalized)
    ).

runtime_noise_line(Line) :-
    sub_string(Line, 0, _, _, "MORK init:").

assertion_surface_line(Line) :-
    sub_string(Line, 0, 3, _, "is ").

assertion_surface_status(Line, pass) :-
    sub_string(Line, _, _, _, "✅"),
    !.
assertion_surface_status(Line, fail) :-
    sub_string(Line, _, _, _, "❌"),
    !.
assertion_surface_status(Line, raw(Line)).

string_empty("").

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
    path_fixture(RelPath, Source),
    directory_file_path(FixtureRoot, RelPath, Dest),
    file_directory_name(Dest, DestDir),
    make_directory_path(DestDir),
    copy_file(Source, Dest).

path_fixture(RelPath, Path) :-
    path_generated('source_fixture', Root),
    directory_file_path(Root, RelPath, Path).

path_generated(RelPath, Path) :-
    source_file(run_path_compat_tests, SourceFile),
    file_directory_name(SourceFile, SourceDir),
    directory_file_path(SourceDir, '.generated_path_compat', CompatDir),
    directory_file_path(CompatDir, RelPath, Path).

setup_path_compat_fixture :-
    path_generated('source_fixture', Root),
    path_generated('out', OutRoot),
    path_generated('inplace_fixture', InplaceRoot),
    path_generated('bundle_he', BundleHeRoot),
    path_generated('bundle_petta_library', BundlePettaRoot),
    (   exists_directory(Root)
    ->  delete_directory_and_contents(Root)
    ;   true
    ),
    (   exists_directory(OutRoot)
    ->  delete_directory_and_contents(OutRoot)
    ;   true
    ),
    (   exists_directory(InplaceRoot)
    ->  delete_directory_and_contents(InplaceRoot)
    ;   true
    ),
    (   exists_directory(BundleHeRoot)
    ->  delete_directory_and_contents(BundleHeRoot)
    ;   true
    ),
    (   exists_directory(BundlePettaRoot)
    ->  delete_directory_and_contents(BundlePettaRoot)
    ;   true
    ),
    make_directory_path(OutRoot),
    write_fixture_relative(Root, 'test_import_nested_depth.metta',
        "!(import! &deep support/import_deep/root.metta)\n"),
    write_fixture_relative(Root, 'test_import_modules.metta',
        "!(register-module! support/import_pkg)\n!(import! &db import_pkg:moduleA)\n!(import! &facts import_pkg:data:Facts)\n"),
    write_fixture_relative(Root, 'test_import_foreign_python_file.metta',
        "!(import! &self support/import_foreign_pyfile)\n"),
    write_fixture_relative(Root, 'test_he_eq_surface.metta',
        "(: T Type)\n(= (= $x $x) T)\n!(= Socrates Socrates)\n"),
    write_fixture_relative(Root, 'test_he_reserved_head_order_surface.metta',
        "!(let $x foo (is-space $x))\n(: is-space (-> Atom Bool))\n(= (is-space $atom) T)\n"),
    write_fixture_relative(Root, 'test_he_doc_surface.metta',
        "(@doc foo (@desc \"Doc\"))\n!(get-doc foo)\n"),
    write_fixture_relative(Root, 'test_hyperpose_surface.metta',
        "!(test (once (hyperpose ((slow-branch) (cheap-branch)))) True)\n"),
    write_fixture_relative(Root, 'test_cut_surface.metta',
        "(foo 1)\n(foo 2)\n(= (match-single $space $pat $ret) (let* (($x (match $space $pat $ret)) ($temp (cut))) $x))\n!(match-single &self (foo $1) $1)\n"),
    write_fixture_relative(Root, 'test_raw_cut_surface.metta',
        "!(progn (cut) reached)\n"),
    write_fixture_relative(Root, 'test_msort_surface.metta',
        "(foo 1)\n(foo 1)\n(foo 2)\n!(test (msort (collapse (match &self (foo $x) $x))) (1 1 2))\n"),
    write_fixture_relative(Root, 'test_raw_msort_surface.metta',
        "!(msort (collapse (match &self $x $x)))\n"),
    write_fixture_relative(Root, 'test_length_surface.metta',
        "!(length (1 2 3))\n"),
    write_fixture_relative(Root, 'test_reverse_surface.metta',
        "!(reverse (1 2 3))\n"),
    write_fixture_relative(Root, 'test_last_surface.metta',
        "!(last (1 2 3))\n"),
    write_fixture_relative(Root, 'test_foldl_surface.metta',
        "(= (snoc $x $acc) (append $acc ($x)))\n!(foldl snoc (1 2 3) ())\n"),
    write_fixture_relative(Root, 'test_alpha_unique_atom_surface.metta',
        "!(alpha-unique-atom ((link $x human) (link $y human) (child $z human)))\n"),
    write_fixture_relative(Root, 'test_alpha_equal_surface.metta',
        "!(test (=alpha (alpha-unique-atom ((link $x human) (link $y human) (child $z human))) ((link $a human) (child $b human))) True)\n"),
    write_fixture_relative(Root, 'test_runtime_surface_raw_tuple.metta',
        "(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))\n(= (probe) ((within (fib 5)) (call-within (call (fib 5))) (quote-within (quote (fib 5))) (eval-within (eval (fib 5))) (reduce-within (reduce (fib 5)))))\n"),
    write_fixture_relative(Root, 'test_minmax_surface.metta',
        "!(max 2 (min 1 3))\n"),
    write_fixture_relative(Root, 'test_second_from_pair_surface.metta',
        "!(second-from-pair (A B))\n"),
    write_fixture_relative(Root, 'test_second_from_pair_user_surface.metta',
        "(= (second-from-pair $pair) custom)\n!(second-from-pair (A B))\n"),
    write_fixture_relative(Root, 'test_mixed_test_surface.metta',
        "!(test (+ 1 2) 3)\n!(test (if $x yes no) (yes no))\n"),
    write_fixture_relative(Root, 'test_partial_builtin_surface.metta',
        "(= (inc) (+ 1))\n!(inc 2)\n"),
    write_fixture_relative(Root, 'test_partial_builtin_helper_collision.metta',
        "(= (petta-partial-1 $x) user-defined)\n(= (inc) (+ 1))\n!(inc 2)\n"),
    write_fixture_relative(Root, 'test_partial_composition_surface.metta',
        "(= (.. $f1 $f2 $arg) ($f1 ($f2 $arg)))\n(= (plus1times2) (.. (* 2) (+ 1)))\n!(test (plus1times2 1) 4)\n"),
    write_fixture_relative(Root, 'test_exprdata_callable_surface.metta',
        "(: map-flat3 (-> Expression %Undefined%))\n(= (map-flat3 ($f ())) ())\n(= (map-flat3 ($f (cons $x $xs))) (cons ($f $x) (map-flat3 ($f $xs))))\n(: map-flat4 (-> Expression %Undefined%))\n(= (map-flat4 ($v ($f ()))) ())\n(= (map-flat4 ($v ($f (cons $x $xs)))) (cons ($f $x) (map-flat4 ($v ($f $xs)))))\n(= (p1 $x) (+ 1 $x))\n!(test (map-flat3 (p1 (1 2))) (2 3))\n!(test (map-flat4 (x (p1 (1 2)))) (2 3))\n"),
    write_fixture_relative(Root, 'test_variable_head_boundary_runtime.metta',
        "(= (myfunc2 $mylambda) ($mylambda 43 44))\n!(test (let ($x $y) (1 2) ($x $y)) (1 2))\n!(test (let* ((($x $y) (1 2)) ($z 3)) ($x $y $z)) (1 2 3))\n!(test (let* (($k 45) ($lambda (|-> ($x $y) (42 $x $y $k)))) (myfunc2 $lambda)) (42 43 44 45))\n"),
    write_fixture_relative(Root, 'test_variable_head_boundary_behavior.metta',
        "(= (myfunc2 $mylambda) ($mylambda 43 44))\n!(let ($x $y) (1 2) ($x $y))\n!(let* ((($x $y) (1 2)) ($z 3)) ($x $y $z))\n!(let* (($k 45) ($lambda (|-> ($x $y) (42 $x $y $k)))) (myfunc2 $lambda))\n"),
    write_fixture_relative(Root, 'test_functionhead_guard_surface.metta',
        "(= (in $x $L) (let True (is-member $x $L) $x))\n(= (myplus (in $X (1 2 3)) (in $Y (2 3))) (in (+ $X $Y) (3 4 5)))\n!(test (collapse (myplus $x $y)) (3 4 4 5 5))\n"),
    write_fixture_relative(Root, 'test_functionhead_duplicate_surface.metta',
        "(= (same $x $x) ok)\n"),
    write_fixture_relative(Root, 'test_functionhead_append_suffix_surface.metta',
        "(= (myfunc $A $B) (append (append (42) $A) $B))\n(= (h (myfunc (10) $B) $C) ($B $C))\n"),
    write_fixture_relative(Root, 'test_functionhead_eq_guard_surface.metta',
        "(= (myfunc $A $B) (append (append (42) $A) $B))\n(= (h_unify $A $C) (if (= $A (myfunc (10) $B)) ($B $C) (empty)))\n"),
    write_fixture_relative(Root, 'test_function_call_inversion_structural_let_surface.metta',
        "(= (f $Head $Tail) (append ($Head) $Tail))\n(= (probe) (let (f $Head $Tail) (1 2 3 4) ($Head $Tail)))\n"),
    write_fixture_relative(Root, 'test_function_call_inversion_arith_let_surface.metta',
        "(= (g $X $Y $Z) (append ((#+ $X $Z)) $Y))\n(= (probe) (let (g $X $Y 35) (42 2 3) ($X $Y 40)))\n"),
    write_fixture_relative(Root, 'test_profile_native_test_surface.metta',
        "(: wu1 (-> Number Expression Expression))\n(= (wu1 $a $b) (42 $a $b))\n!(test (wu1 (+ 2 4) (+ 4 2)) (quote (42 6 (+ 4 2))))\n"),
    write_fixture_relative(Root, 'test_profile_eval_surface.metta',
        "(= (f $L $a $b) (let $result (+ $a $b) (append ($result) $L)))\n!(test (let $fbody_specialized (match &self (= (f (42) 40.7 2) $x) $x) (eval $fbody_specialized)) (42.7 42))\n(= (evalCustom $body) (let* (($a (add-atom &self (= (myfunc) $body))) ($res (reduce (myfunc))) ($r (remove-atom &self (= (myfunc) $body)))) $res))\n!(test (evalCustom (match &self (= (f (42) 40.7 2) $x) $x)) (42.7 42))\n"),
    write_fixture_relative(Root, 'test_local_import_materialization.metta',
        "!(import! &self support/local_dep_lib.metta)\n!(test (dep-f 2) 3)\n"),
    write_fixture_relative(Root, 'test_library_import_materialization.metta',
        "!(import! &self (library lib_roman))\n!(test (map-flat (+ 1) (1 2 3)) (2 3 4))\n"),
    write_fixture_relative(Root, 'test_imported_dependency_blocker.metta',
        "!(import! &self support/imported_blocker.metta)\n!(test blocker ())\n"),
    write_fixture_relative(Root, 'support/import_deep/root.metta',
        "(deep-root loaded)\n!(import! &self level1/Mid.metta)\n"),
    write_fixture_relative(Root, 'support/import_deep/level1/Mid.metta',
        "(deep-mid loaded)\n!(import! &self level2/Leaf.metta)\n!(import! &self ../shared/Helper.metta)\n"),
    write_fixture_relative(Root, 'support/import_deep/level1/level2/Leaf.metta',
        "(deep-leaf loaded)\n!(import! &self ../../shared/LeafHelper.metta)\n"),
    write_fixture_relative(Root, 'support/import_deep/shared/Helper.metta',
        "(deep-helper loaded)\n"),
    write_fixture_relative(Root, 'support/import_deep/shared/LeafHelper.metta',
        "(deep-leaf-helper loaded)\n"),
    write_fixture_relative(Root, 'support/import_pkg/moduleA.metta',
        "(pkg-root loaded)\n!(import! &self Helper)\n"),
    write_fixture_relative(Root, 'support/import_pkg/Helper.metta',
        "(pkg-helper loaded)\n"),
    write_fixture_relative(Root, 'support/import_pkg/data/Facts.metta',
        "(item alpha)\n(item beta)\n"),
    write_fixture_relative(Root, 'support/local_dep_lib.metta',
        "(= (dep-f $x) (+ $x 1))\n"),
    write_fixture_relative(Root, 'support/imported_blocker.metta',
        "!(msort (collapse (match &self $x $x)))\n"),
    write_fixture_relative(Root, 'lib/lib_roman.metta',
        "(= (map-flat $f ()) ())\n(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))\n(= (/==\\ $a $b) (/?\\ == $a $b))\n(= (\\== $a $b) (\\? == $a $b))\n(= (\\==/ $a $b) (\\?/ == $a $b))\n").

write_fixture_relative(Root, RelPath, Text) :-
    directory_file_path(Root, RelPath, Path),
    file_directory_name(Path, Dir),
    make_directory_path(Dir),
    setup_call_cleanup(
        open(Path, write, Stream),
        write(Stream, Text),
        close(Stream)
    ).

write_toplevel_atom(Stream, exec(Expr)) :-
    write(Stream, '!'),
    print_sexpr(Stream, Expr),
    nl(Stream).
write_toplevel_atom(Stream, plain(Expr)) :-
    print_sexpr(Stream, Expr),
    nl(Stream).

maybe_inline_he_entry_helpers(Direction, SeenIn, Atoms, FinalAtoms) :-
    (   he2petta_direction_name(Direction),
        SeenIn == [],
        translated_items_need_inline_he_helpers(Atoms, HelperHeads),
        HelperHeads \== []
    ->  he_inline_helper_items(HelperHeads, HelperItems),
        splice_he_helper_items_before_first_use(Atoms, HelperHeads, HelperItems, FinalAtoms)
    ;   FinalAtoms = Atoms
    ).

translated_items_need_inline_he_helpers(Items, HelperHeads) :-
    findall(Head,
            translated_items_need_inline_he_helper(Items, Head),
            RawHeads),
    he_inline_helper_head_closure(RawHeads, HelperHeads).

translated_items_need_inline_he_helper(Items, Head) :-
    he_inline_runtime_head(Head),
    translated_items_use_named_head(Items, Head).

translated_items_use_named_head(Items, Head) :-
    is_list(Items),
    member(Item, Items),
    item_payload(Item, Term),
    term_uses_named_head(Term, Head),
    !.

he_inline_runtime_head('assert-results-equal').
he_inline_runtime_head('assert-result-sets-equal').
he_inline_runtime_head('assert-alpha-results-equal').
he_inline_runtime_head('assert-alpha-result-sets-equal').
he_inline_runtime_head('assert-unit').
he_inline_runtime_head('assert-includes').
he_inline_runtime_head('assert-equal-msg').
he_inline_runtime_head('assert-results-equal-msg').
he_inline_runtime_head('call-or-inert').
he_inline_runtime_head('change-state-with-source').
he_inline_runtime_head('match-template-eval').

he_inline_helper_head_closure(Heads0, Heads) :-
    sort(Heads0, Seed),
    he_inline_helper_head_closure_fixpoint(Seed, Heads).

he_inline_helper_head_closure_fixpoint(Heads0, Heads) :-
    findall(Dep,
            ( member(Head, Heads0),
              he_inline_helper_head_dependency(Head, Dep)
            ),
            RawDeps),
    append(Heads0, RawDeps, Heads1),
    sort(Heads1, Sorted),
    (   Sorted == Heads0
    ->  Heads = Sorted
    ;   he_inline_helper_head_closure_fixpoint(Sorted, Heads)
    ).

he_inline_helper_head_dependency('assert-results-equal', 'results-bag-equal').
he_inline_helper_head_dependency('assert-result-sets-equal', 'normalize-states').
he_inline_helper_head_dependency('assert-result-sets-equal', 'state-normal-form').
he_inline_helper_head_dependency('assert-result-sets-equal', 'results-bag-equal').
he_inline_helper_head_dependency('assert-alpha-results-equal', 'alpha-bag-equal').
he_inline_helper_head_dependency('assert-alpha-results-equal', 'alpha-bag-remove-one').
he_inline_helper_head_dependency('assert-alpha-result-sets-equal', 'normalize-states').
he_inline_helper_head_dependency('assert-alpha-result-sets-equal', 'state-normal-form').
he_inline_helper_head_dependency('assert-alpha-result-sets-equal', 'alpha-bag-equal').
he_inline_helper_head_dependency('assert-alpha-result-sets-equal', 'alpha-bag-remove-one').
he_inline_helper_head_dependency('assert-equal-msg', 'results-bag-equal').
he_inline_helper_head_dependency('assert-results-equal-msg', 'results-bag-equal').
he_inline_helper_head_dependency('call-or-inert', 'eval-or-inert').
he_inline_helper_head_dependency('match-template-eval', 'match-template-eval-if').
he_inline_helper_head_dependency('match-template-eval', 'match-template-eval-application').

he_inline_helper_items(HelperHeads, Items) :-
    he_helper_template_path(TemplatePath),
    read_metta_file(TemplatePath, HelperAtoms0),
    include(he_inline_helper_atom(HelperHeads), HelperAtoms0, HelperAtoms),
    wrap_plain_items(HelperAtoms, Items).

he_helper_template_path(TemplatePath) :-
    source_file(run_path_compat_tests, SourceFile),
    file_directory_name(SourceFile, SourceDir),
    directory_file_path(SourceDir, '../PeTTa/lib/lib_he.metta', RelPath),
    absolute_file_name(RelPath, TemplatePath, [solutions(first)]).

he_inline_helper_atom(HelperHeads, ['=', [Head|_], _]) :-
    memberchk(Head, HelperHeads),
    !.
he_inline_helper_atom(_, _) :-
    fail.

splice_he_helper_items_before_first_use(Items, HelperHeads, HelperItems, Spliced) :-
    splice_he_helper_items_before_first_use_acc(Items, HelperHeads, HelperItems, Spliced, false).

splice_he_helper_items_before_first_use_acc([], _, HelperItems, HelperItems, false) :- !.
splice_he_helper_items_before_first_use_acc([], _, _, [], true).
splice_he_helper_items_before_first_use_acc([Item|Items], HelperHeads, HelperItems, Spliced, false) :-
    item_payload(Item, Term),
    term_uses_any_named_head(Term, HelperHeads),
    !,
    append(HelperItems, [Item|Items], Spliced).
splice_he_helper_items_before_first_use_acc([Item|Items], HelperHeads, HelperItems, [Item|Spliced], Inserted0) :-
    splice_he_helper_items_before_first_use_acc(Items, HelperHeads, HelperItems, Spliced, Inserted0).

term_uses_any_named_head(Term, [Head|_]) :-
    term_uses_named_head(Term, Head),
    !.
term_uses_any_named_head(Term, [_|Heads]) :-
    term_uses_any_named_head(Term, Heads).

maybe_materialize_petta_helper_libs(Atoms, OutPath) :-
    (   translated_items_import_lib_petta(Atoms)
    ->  ensure_translator_helper_file(OutPath, 'lib_petta.metta')
    ;   true
    ).

translated_items_import_lib_petta(Atoms) :-
    is_list(Atoms),
    member(Item, Atoms),
    item_payload(Item, ['import!', '&self', lib_petta]),
    !.

ensure_translator_helper_file(OutPath, HelperName) :-
    translator_helper_template_path(HelperName, TemplatePath),
    file_directory_name(OutPath, OutDir),
    directory_file_path(OutDir, HelperName, TargetPath),
    ensure_matching_helper_copy(TemplatePath, TargetPath).

translator_helper_template_path(HelperName, TemplatePath) :-
    source_file(run_path_compat_tests, SourceFile),
    file_directory_name(SourceFile, SourceDir),
    directory_file_path(SourceDir, HelperName, TemplatePath).

ensure_matching_helper_copy(TemplatePath, TargetPath) :-
    (   exists_file(TargetPath)
    ->  read_file_to_string(TemplatePath, TemplateText, []),
        read_file_to_string(TargetPath, TargetText, []),
        (   TemplateText == TargetText
        ->  true
        ;   throw(error(permission_error(overwrite, file, TargetPath),
                        context(test_on_real_files:ensure_matching_helper_copy/2,
                                'refusing to overwrite existing helper file with different contents')))
        )
    ;   copy_file(TemplatePath, TargetPath)
    ).

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

safe_translate_pe_hyperpose(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_hyperpose(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_ffi_tokens(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_ffi_tokens(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_ffi_tokens(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_ffi_tokens(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_petta_he(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_petta_he(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_petta_he(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_petta_he(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_petta_he_hyperpose(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_petta_he_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_petta_he_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_petta_he_hyperpose(A, Raw),
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

safe_translate_pe_hyperpose_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_hyperpose(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_hyperpose(A, TA)
    ;   pe_translate_term_hyperpose(A, TA)
    ).

safe_translate_pe_petta_he_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_petta_he(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_petta_he(A, TA)
    ;   pe_translate_term_petta_he(A, TA)
    ).

safe_translate_pe_petta_he_hyperpose_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_petta_he_hyperpose(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_petta_he_hyperpose(A, TA)
    ;   pe_translate_term_petta_he_hyperpose(A, TA)
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

safe_translate_pe_extended_hyperpose(A, TA) :-
    (   A = ['=', _, _]
    ->  pe_translate_decl_ext_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   A = [':', _, _]
    ->  pe_translate_decl_ext_hyperpose(A, Raw),
        pe_optimize_decl(Raw, TA)
    ;   pe_translate_term_ext_hyperpose(A, Raw),
        pe_optimize_term(Raw, TA)
    ).

safe_translate_pe_extended_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_ext(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_ext(A, TA)
    ;   pe_translate_term_ext(A, TA)
    ).

safe_translate_pe_extended_hyperpose_raw(A, TA) :-
    (   A = ['=', _, _] -> pe_translate_decl_ext_hyperpose(A, TA)
    ;   A = [':', _, _] -> pe_translate_decl_ext_hyperpose(A, TA)
    ;   pe_translate_term_ext_hyperpose(A, TA)
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
