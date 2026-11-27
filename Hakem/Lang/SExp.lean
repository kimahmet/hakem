/-!
# Hakem dili — okuyucu

Belgeler S-ifadeleridir: atomlar ve parantezli listeler. `;` satır sonuna kadar yorumdur.
Bu dosya metni ağaca çevirir; anlam içermez. Küçüktür ve bağımsız olarak yeniden
yazılabilir.
-/

inductive SExp where
  | atom : String → SExp
  | list : List SExp → SExp
  deriving Repr, Inhabited

inductive Tok where
  | lp
  | rp
  | atom (s : String)
  deriving Repr, DecidableEq

def flushTok (buf : List Char) (acc : List Tok) : List Tok :=
  if buf.isEmpty then acc else Tok.atom (String.ofList buf.reverse) :: acc

def isSpace (c : Char) : Bool := c = ' ' || c = '\n' || c = '\t' || c = '\r'

/-- Karakterlerden simgeler. `buf`: biriken atom (ters), `cmt`: yorum içinde mi. -/
def tokenizeAux : List Char → List Char → Bool → List Tok → List Tok
  | [],      buf, _,     acc => (flushTok buf acc).reverse
  | c :: cs, buf, true,  acc => tokenizeAux cs buf (c != '\n') acc
  | c :: cs, buf, false, acc =>
    if c = ';' then tokenizeAux cs [] true (flushTok buf acc)
    else if c = '(' then tokenizeAux cs [] false (Tok.lp :: flushTok buf acc)
    else if c = ')' then tokenizeAux cs [] false (Tok.rp :: flushTok buf acc)
    else if isSpace c then tokenizeAux cs [] false (flushTok buf acc)
    else tokenizeAux cs (c :: buf) false acc

def tokenize (s : String) : List Tok := tokenizeAux s.toList [] false []

/-- Yığınlı ayrıştırıcı. Yığının her katı, açık bir listenin (ters) öğeleridir. -/
def parseToks : List Tok → List (List SExp) → Option (List SExp)
  | [],            [acc]               => some acc.reverse
  | [],            _                   => none
  | .lp :: ts,     st                  => parseToks ts ([] :: st)
  | .rp :: ts,     cur :: parent :: st => parseToks ts ((SExp.list cur.reverse :: parent) :: st)
  | .rp :: _,      _                   => none
  | .atom a :: ts, cur :: st           => parseToks ts ((SExp.atom a :: cur) :: st)
  | .atom _ :: _,  []                  => none

def readSExps (s : String) : Option (List SExp) := parseToks (tokenize s) [[]]
