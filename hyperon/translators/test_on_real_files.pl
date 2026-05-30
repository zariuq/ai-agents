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
                             petta_test_results_fun/1 as pe_petta_test_results_fun,
                             petta_test_bag_fun/1 as pe_petta_test_bag_fun,
                             petta_test_normalize_fun/1 as pe_petta_test_normalize_fun,
                             petta_lambda_fun/1 as pe_petta_lambda_fun,
                             petta_apply1_fun/1 as pe_petta_apply1_fun,
                             petta_apply2_fun/1 as pe_petta_apply2_fun,
                             petta_ffi_function_call_inversion_fun/1 as pe_petta_ffi_function_call_inversion_fun,
                             petta_lib_petta_helper_decls/2 as pe_petta_lib_petta_helper_decls,
                             test_call_needs_collapse/1 as pe_test_call_needs_collapse,
                             test_call_needs_bag_equality/1 as pe_test_call_needs_bag_equality,
                             petta_state_clear_fun/1 as pe_petta_state_clear_fun,
                             petta_state_set_fun/1 as pe_petta_state_set_fun,
                             petta_state_get_fun/1 as pe_petta_state_get_fun,
                             petta_state_cell_fun/1 as pe_petta_state_cell_fun]).

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
        length(Atoms, N),
        setup_call_cleanup(
            open(AbsOutPath, write, Stream),
            once((
                write_translation_header(Stream, Direction, AbsInPath, N),
                translate_toplevel_atoms(Direction, Atoms, TAtoms),
                relocate_local_module_surfaces(AbsInPath, AbsOutPath, TAtoms, CompatAtoms),
                forall(member(TA, CompatAtoms), write_toplevel_atom(Stream, TA)),
                maybe_materialize_petta_helper_libs(CompatAtoms, AbsOutPath)
            )),
            close(Stream)
        )
    ).

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
    translate_toplevel_atoms_acc(Direction, Atoms, Atoms, TAtoms0),
    postprocess_toplevel_atoms(Direction, Atoms, TAtoms0, TAtoms).

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
    translate_term_for(Direction, Expr, TExpr),
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).
translate_toplevel_atoms_acc(Direction, SourceAtoms, [A | Rest], [plain(TA) | TRest]) :-
    translate_toplevel_atom(Direction, A, TA),
    translate_toplevel_atoms_acc(Direction, SourceAtoms, Rest, TRest).

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
    sort(RawKeys, HelperKeys).

translated_items_need_lib_petta_helper(_Direction, SourceAtoms, _Items, second_from_pair) :-
    source_program_uses_second_from_pair(SourceAtoms),
    \+ source_program_defines_second_from_pair(SourceAtoms).
translated_items_need_lib_petta_helper(Direction, SourceAtoms, _Items, is_member) :-
    \+ petta_he_profile_direction(Direction),
    source_program_uses_is_member(SourceAtoms),
    \+ source_program_defines_is_member(SourceAtoms).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_equal) :-
    translated_items_use_named_helper(Items, pe_petta_test_equal_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_results) :-
    translated_items_use_named_helper(Items, pe_petta_test_results_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, test_bag) :-
    translated_items_use_named_helper(Items, pe_petta_test_bag_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, lambda) :-
    translated_items_use_named_helper(Items, pe_petta_lambda_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, apply1) :-
    translated_items_use_named_helper(Items, pe_petta_apply1_fun).
translated_items_need_lib_petta_helper(_Direction, _SourceAtoms, Items, apply2) :-
    translated_items_use_named_helper(Items, pe_petta_apply2_fun).
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
    maplist(lib_petta_helper_uses_default_names, HelperKeys).

lib_petta_helper_uses_default_names(second_from_pair).
lib_petta_helper_uses_default_names(is_member).
lib_petta_helper_uses_default_names(test_equal) :-
    pe_petta_test_equal_fun('petta-test-equal').
lib_petta_helper_uses_default_names(test_results) :-
    pe_petta_test_results_fun('petta-test-results'),
    pe_petta_test_normalize_fun('petta-normalize-results').
lib_petta_helper_uses_default_names(test_bag) :-
    pe_petta_test_bag_fun('petta-test-bag-equal').
lib_petta_helper_uses_default_names(lambda) :-
    pe_petta_lambda_fun('petta-lambda').
lib_petta_helper_uses_default_names(apply1) :-
    pe_petta_apply1_fun('petta-apply1'),
    pe_petta_lambda_fun('petta-lambda').
lib_petta_helper_uses_default_names(apply2) :-
    pe_petta_apply2_fun('petta-apply2'),
    pe_petta_apply1_fun('petta-apply1'),
    pe_petta_lambda_fun('petta-lambda').
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
                          [TestFun, RActual, RExpected]) :-
    !,
    builtin_test_helper_head(Actual, TestFun),
    rewrite_builtin_test_term(Actual, RActual),
    rewrite_builtin_test_term(Expected, RExpected).
rewrite_builtin_test_term(List, Rewritten) :-
    is_list(List), !,
    maplist(rewrite_builtin_test_term, List, Rewritten).
rewrite_builtin_test_term(Term, Term).

builtin_test_helper_head(Actual, 'petta-test-bag-equal') :-
    pe_test_call_needs_bag_equality(Actual),
    !.
builtin_test_helper_head(Actual, 'petta-test-results') :-
    pe_test_call_needs_collapse(Actual),
    !.
builtin_test_helper_head(_, 'petta-test-equal').

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
    forall(path_compat_case(N, Name, Goal), run_path_compat_case(N, Name, Goal)).

run_path_compat_case(N, Name, Goal) :-
    (   call(Goal)
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n", [N, Name]),
        fail
    ).

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
        file_contains_text(EntryOut,
            "!(import! &db support/import_pkg/moduleA.he2petta.metta)"),
        exists_file(ModuleOut),
        file_contains_text(ModuleOut,
            "!(import! &self Helper.he2petta.metta)")
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
            "!(import! &deep support/import_deep/root.metta)"),
        exists_file(RootOut)
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

path_compat_case(9, "PeTTa->HE file translation routes test calls through lib_petta",
    (   path_fixture('test_hyperpose_surface.metta', Source),
        path_generated('out/test_hyperpose_surface.with_test.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "petta-test-"),
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

path_compat_case(13, "default PeTTa->HE file translation lowers assertion-only msort to bag equality",
    (   path_fixture('test_msort_surface.metta', Source),
        path_generated('out/test_msort_surface.he.metta', Output),
        path_generated('out/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "petta-test-bag-equal"),
        exists_file(HelperOut),
        file_contains_text(HelperOut, "(= (petta-test-bag-equal $actual $expected)")
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

path_compat_case(19, "mixed test surfaces route per call instead of per file",
    (   path_fixture('test_mixed_test_surface.metta', Source),
        path_generated('out/test_mixed_test_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "!(petta-test-equal (+ 1 2) 3)"),
        file_contains_text(Output, "!(petta-test-results (if $x yes no) (yes no))")
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

path_compat_case(24, "PeTTa->HE file translation rewrites builtin partials to local helpers",
    (   path_fixture('test_partial_builtin_surface.metta', Source),
        path_generated('out/partial_builtin/test_partial_builtin_surface.he.metta', Output),
        path_generated('out/partial_builtin/lib_petta.metta', HelperOut),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "lib_petta"),
        file_contains_text(Output, "(= (petta-partial-1 $__tr_"),
        file_contains_text(Output, "(= (inc) petta-partial-1)"),
        file_contains_text(Output, "!((inc) 2)"),
        \+ exists_file(HelperOut)
    )).

path_compat_case(25, "generated builtin partial helper names avoid source collisions",
    (   path_fixture('test_partial_builtin_helper_collision.metta', Source),
        path_generated('out/partial_builtin_collision/test_partial_builtin_helper_collision.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        \+ file_contains_text(Output, "!(import! &self lib_petta)"),
        file_contains_text(Output, "(= (petta-partial-1 $x) user-defined)"),
        file_contains_text(Output, "(= (petta-partial-2 $__tr_"),
        file_contains_text(Output, "(= (inc) petta-partial-2)")
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
        file_contains_text(Output, "!(petta-test-results (map-flat3 (quote (p1 (1 2)))) (2 3))"),
        file_contains_text(Output, "!(petta-test-results (map-flat4 (quote (x (p1 (1 2))))) (2 3))")
    )).

path_compat_case(28, "Closed unary callable composition rewrites to a reusable helper symbol",
    (   path_fixture('test_partial_composition_surface.metta', Source),
        path_generated('out/test_partial_composition_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (petta-partial-1 $__tr_"),
        file_contains_text(Output, "(= (petta-partial-2 $__tr_"),
        file_contains_text(Output, "(= (petta-partial-3 $__tr_"),
        file_contains_text(Output, "(= (plus1times2) petta-partial-3)"),
        file_contains_text(Output, "!(petta-test-equal ((plus1times2) 1) 4)")
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
        file_contains_text(Output, "($fun $C))")
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
        file_contains_text(Output, "($fun $C))")
    )).

path_compat_case(33, "pure structural function-call inversion let-patterns lower through decons",
    (   path_fixture('test_function_call_inversion_structural_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_structural_let_surface.he.metta', Output),
        translate_file_petta_to_he(Source, Output),
        file_contains_text(Output, "(= (probe) (chain (decons-atom (1 2 3 4))"),
        file_contains_text(Output, "(first-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(second-from-pair $__tr_head_pair_"),
        file_contains_text(Output, "(eval (atom-subst $Head $fun ($fun $Tail)))"),
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
        file_contains_text(Output, "(eval (atom-subst $X $fun ($fun $Y 40)))"),
        \+ file_contains_text(Output, "(petta-apply2 $X $Y 40)")
    )).

path_compat_case(36, "ffi-tokens mode lowers arithmetic function-call inversion to explicit ffi surface",
    (   path_fixture('test_function_call_inversion_arith_let_surface.metta', Source),
        path_generated('out/test_function_call_inversion_arith_let_surface.ffi_tokens.metta', Output),
        translate_file_petta_to_he_ffi_tokens(Source, Output),
        file_contains_text(Output, "(= (probe) (petta-ffi-function-call-inversion arithmetic-append-suffix"),
        file_contains_text(Output, "(quote (g $X $Y 35))"),
        file_contains_text(Output, "(eval (atom-subst $X $fun ($fun $Y 40)))"),
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
