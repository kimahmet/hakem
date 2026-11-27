/-!
# Hakem language — reader

Documents are S-expressions: atoms and parenthesised lists. `;` starts a comment to end of line.
This file turns text into a tree; it carries no meaning. It is small and can be
re-implemented independently.
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

/-- Characters to tokens. `buf`: the atom being read (reversed); `cmt`: inside a comment. -/
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

/-- Stack parser. Each stack level holds the (reversed) elements of an open list. -/
def parseToks : List Tok → List (List SExp) → Option (List SExp)
  | [],            [acc]               => some acc.reverse
  | [],            _                   => none
  | .lp :: ts,     st                  => parseToks ts ([] :: st)
  | .rp :: ts,     cur :: parent :: st => parseToks ts ((SExp.list cur.reverse :: parent) :: st)
  | .rp :: _,      _                   => none
  | .atom a :: ts, cur :: st           => parseToks ts ((SExp.atom a :: cur) :: st)
  | .atom _ :: _,  []                  => none

def readSExps (s : String) : Option (List SExp) := parseToks (tokenize s) [[]]
