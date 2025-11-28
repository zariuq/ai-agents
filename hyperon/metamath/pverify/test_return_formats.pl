% test_return_formats.pl - Test what Prolog can return to MeTTa
:- module(test_return_formats, [return_atom/1, return_list/1, return_compound/1]).

return_atom(myatom).

return_list([a, b, c]).

return_compound(c([a, b, c])).
