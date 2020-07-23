(* Read file to string *)
fun file_to_string name = let
  val f = TextIO.openIn name
  val s = TextIO.inputAll f
  val _ = TextIO.closeIn f
in s end

fun fs fname = Fsort.fsort_string
  (String.tokens (not o Char.isAlpha) (String.map (Char.toLower) (file_to_string fname)))

val r = fs "/home/ladmin/Teaching/FDS/SS19/fds17/SS19//Exercises//ex14/MASC-3.0.0/data/written/non-fiction/chZ.txt"
