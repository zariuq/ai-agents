Definition if_simple : set := if 1 = 0 then Empty else 1.
Definition if_nested : set := if 1 = 0 then (if 0 = 0 then 1 else 2) else 3.
Definition if_app : set := f (if x then y else z).
