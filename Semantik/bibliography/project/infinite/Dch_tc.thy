
theory Dch_tc imports Dch Dtc begin
(* monad morphism from total correctness monad to chorus angelorum monad *)
consts
  tc2ch :: "'a set TorN => 'a uca"

primrec
  tc2ch_Term : "tc2ch (Term A) = uc_Abs {A}"
  tc2ch_NT : "tc2ch NonTerm = uc_Abs {}"

end

