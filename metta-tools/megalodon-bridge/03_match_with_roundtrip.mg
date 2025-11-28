Definition match_bool : set := match true with | true => false | false => true end.

Definition match_nat : set := match n with | 0 => 0 | S p => p end.

