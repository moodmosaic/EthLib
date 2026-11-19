import Property.Engine.Common
import EthLib.Engine.Jwt

/-!
# The authentication of the Engine API

Tokens that are almost valid, against a model of the Engine profile written from
`authentication.md`, RFC 7515, RFC 7518 and RFC 7519, with PyJWT as a second opinion on the tag.
-/

open Hedgehog Support EthLib EthLib.Engine

namespace EngineProperty

/-- Base64url without padding, RFC 4648 section 5, written here so a token owes EthLib nothing. -/
def base64url (bytes : ByteArray) : String :=
  let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList.toArray
  let sextet (n : Nat) : Char := alphabet.getD (n % 64) 'A'
  let rec go : List UInt8 → List Char
    | a :: b :: c :: rest =>
      let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
      sextet (n / 262144) :: sextet (n / 4096) :: sextet (n / 64) :: sextet n :: go rest
    | [a, b] =>
      let n := a.toNat * 65536 + b.toNat * 256
      [sextet (n / 262144), sextet (n / 4096), sextet (n / 64)]
    | [a] => [sextet (a.toNat / 4), sextet (a.toNat * 16)]
    | [] => []
  String.ofList (go bytes.toList)

/-- White space between the tokens of JSON: the four characters of RFC 8259, and rarely another. -/
def genSpace : Gen String :=
  Gen.frequency [(12, pure ""), (2, pure " "), (1, pure "\n"), (1, pure "\t"), (1, pure "\r "),
    (1, pure "\x0c")]

/-- An object from members, with white space around its tokens. -/
def genObjectText (members : List (String × String)) : Gen String := do
  let parts ← members.mapM fun (key, value) => do
    let (a, b) ← Gen.zip genSpace genSpace
    pure (a ++ key ++ b ++ ":" ++ a ++ value ++ b)
  let body := ",".intercalate parts
  Gen.frequency [(20, pure ("{" ++ body ++ "}")), (1, pure ("{" ++ body ++ ",}")),
    (1, pure ("{" ++ body ++ "} x")), (1, pure ("[" ++ body ++ "]")), (1, pure ("{" ++ body)),
    (1, pure (" {" ++ body ++ "}\n")), (1, pure ("\ufeff{" ++ body ++ "}"))]

/-- A member that a reader must ignore: a claim it does not know, of any JSON form. -/
def genExtraMember : Gen (String × String) :=
  Gen.element [("\"id\"", "\"cl-1\""), ("\"clv\"", "\"teku/v24\""), ("\"exp\"", "1"),
    ("\"nbf\"", "99999999999999999999"), ("\"x\"", "{\"iat\":0,\"alg\":\"none\"}"),
    ("\"a\"", "[1,[true,false,null],{\"b\":-0.5e-3}]"),
    ("\"s\"", "\"\\u00e9\\n\\\"\\ud83d\\ude00\""),
    ("\"e\"", "{}"), ("\"l\"", "[]"), ("\"bad\"", "01"), ("\"bad\"", "\"\\x\""), ("\"t\"", "tru"),
    ("\"iat \"", "0"), ("\"IAT\"", "0"), ("\"n\"", "-0"), ("\"f\"", "1.5E+2")]

/-- The text of an issued-at claim near a clock: a number at the edge of the window, in some form.

The offsets of 59, 60 and 61 seconds either way are where the window ends. -/
def genIatText (clock : Nat) : Gen String := do
  let offset ← Gen.frequency [(6, Gen.element [-61, -60, -59, 59, 60, 61]), (2, pure (0 : Int)),
    (2, Gen.int (.linearFrom 0 (-200) 200))]
  let n : Int := clock + offset
  let d := toString n
  Gen.frequency [(8, pure d), (2, pure (d ++ ".0")), (2, pure (d ++ ".5")),
    (1, pure (d ++ ".000001")), (1, pure (d ++ "0e-1")), (1, pure (d ++ "00E-2")),
    (1, pure (d ++ "e0")), (1, pure (d ++ "E+0")), (1, pure (d ++ "e1")),
    (1, pure (toString (n - 1) ++ ".999999999999999999999")), (1, pure ("\"" ++ d ++ "\"")),
    (1, pure ("0" ++ d)), (1, pure ("+" ++ d)), (1, pure "true"), (1, pure "null"),
    (1, pure ("[" ++ d ++ "]")), (1, pure ("{\"iat\":" ++ d ++ "}")), (1, pure "1e999999999"),
    (1, pure "1e-999999999"), (1, pure "0e999999999"), (1, pure "-1e-999999999"),
    (1, pure (d ++ ".")), (1, pure ("0." ++ d ++ "e" ++ toString d.length)),
    (1, pure ("0.0" ++ d ++ "e" ++ toString (d.length + 1)))]

/-- The text of the claims: an issued-at claim mostly, once or twice, among other claims. -/
def genClaimsText (clock : Nat) : Gen String := do
  let key ← Gen.frequency [(10, pure "\"iat\""), (1, pure "\"\\u0069at\""), (1, pure "\"Iat\"")]
  let iat ← Gen.frequency [(10, List.singleton <$> genIatText clock), (1, pure []),
    (2, Gen.list (.singleton 2) (genIatText clock))]
  let extra ← Gen.list (.linear 0 3) genExtraMember
  let members ← Gen.shuffle (iat.map (key, ·) ++ extra)
  genObjectText members

/-- The text of the header: HS256 mostly, or another algorithm, none, or a critical extension. -/
def genHeaderText : Gen String := do
  let alg ← Gen.frequency [(12, pure ["\"HS256\""]), (1, pure ["\"none\""]),
    (1, pure ["\"HS384\""]),
    (1, pure ["\"hs256\""]), (1, pure ["\"HS256 \""]), (1, pure ["256"]), (1, pure ["null"]),
    (1, pure []), (1, pure ["\"none\"", "\"HS256\""]), (1, pure ["\"HS256\"", "\"none\""]),
    (1, pure ["\"\\u0048S256\""])]
  let key ← Gen.frequency [(10, pure "\"alg\""), (1, pure "\"\\u0061lg\""), (1, pure "\"ALG\"")]
  let rest ← Gen.subsequence [("\"typ\"", "\"JWT\""), ("\"crit\"", "[\"x\"]"), ("\"kid\"", "\"1\""),
    ("\"crit\"", "null")]
  let rest ← Gen.frequency [(4, pure (rest.filter (·.1 != "\"crit\""))), (1, pure rest)]
  let members ← Gen.shuffle (alg.map (key, ·) ++ rest)
  genObjectText members

/-- How a part of a token is encoded: as RFC 7515 asks, or almost. -/
inductive Encoding where
  | plain | padded | trailingBits | standardAlphabet
  deriving Repr, BEq

/-- A part of a token: base64url without padding, or a near miss of it. -/
def encodePart (encoding : Encoding) (text : String) : String :=
  let plain := base64url text.toUTF8
  match encoding with
  | .plain => plain
  | .padded => plain ++ String.ofList (List.replicate ((4 - plain.length % 4) % 4) '=')
  | .trailingBits =>
    -- With two or three characters in the last group, its last character has unused low bits.
    match plain.toList.reverse with
    | 'A' :: rest => if plain.length % 4 == 0 then plain else String.ofList ('B' :: rest).reverse
    | 'Q' :: rest => if plain.length % 4 == 0 then plain else String.ofList ('R' :: rest).reverse
    | 'g' :: rest => if plain.length % 4 == 0 then plain else String.ofList ('h' :: rest).reverse
    | 'w' :: rest => if plain.length % 4 == 0 then plain else String.ofList ('x' :: rest).reverse
    | _ => plain
  | .standardAlphabet => plain.map fun c => if c == '-' then '+' else if c == '_' then '/' else c

/-- What is done to a token after its tag is computed. -/
inductive Damage where
  | none
  /-- Replace the character of the tag at an index by another. -/
  | tagChar (index : Nat) (c : Char)
  | tagPadded | tagEmpty | twoParts | fourParts | emptyHeader | otherSecret | tagTruncated
  /-- The tag of the same parts under a secret of another length. -/
  | swapParts
  deriving Repr, BEq

/-- A token before its tag: its secret, the clock, and its two parts. -/
structure TokenCase where
  secret : ByteArray
  clock : Nat
  header : String
  claims : String
  headerEncoding : Encoding
  claimsEncoding : Encoding
  damage : Damage

instance : Repr TokenCase where
  reprPrec t _ := s!"secret {hex t.secret} clock {t.clock} header {repr t.header} " ++
    s!"({repr t.headerEncoding}) claims {repr t.claims} ({repr t.claimsEncoding}) " ++
    s!"damage {repr t.damage}"

/-- A clock: near zero, where the window reaches below zero, or any time. -/
def genClock : Gen Nat :=
  Gen.frequency [(1, Gen.nat (.linear 0 130)), (3, Gen.nat (.exponential 0 (2 ^ 40))),
    (1, pure 1700000000), (1, (2 ^ 64 - ·) <$> Gen.nat (.linear 0 100))]

/-- A token that is valid, or one step from it. -/
def genTokenCase : Gen TokenCase := do
  let size ← Gen.frequency [(20, pure 32), (1, Gen.element [0, 1, 16, 31, 33, 64, 65])]
  let secret ← genBytes (.singleton size)
  let clock ← genClock
  let encoding := Gen.frequency [(12, pure Encoding.plain), (1, pure .padded),
    (1, pure .trailingBits), (1, pure .standardAlphabet)]
  let damage := Gen.frequency [(16, pure Damage.none),
    (2, Gen.zipWith Damage.tagChar (Gen.nat (.constant 0 42)) (Gen.element "ABQgwx-_9=. ".toList)),
    (1, Gen.element [Damage.tagPadded, .tagEmpty, .twoParts, .fourParts, .emptyHeader,
      .otherSecret, .tagTruncated, .swapParts])]
  let ((header, claims), (he, ce), damage) ←
    Gen.zip (Gen.zip genHeaderText (genClaimsText clock))
      (Gen.zip (Gen.zip encoding encoding) damage)
  pure ⟨secret, clock, header, claims, he, ce, damage⟩

/-- The compact token of a case, given its tag. -/
def TokenCase.token (t : TokenCase) (tag : String) : String :=
  let h := encodePart t.headerEncoding t.header
  let c := encodePart t.claimsEncoding t.claims
  match t.damage with
  | .none | .otherSecret => s!"{h}.{c}.{tag}"
  | .tagChar index ch => s!"{h}.{c}.{String.ofList (tag.toList.set index ch)}"
  | .tagPadded => s!"{h}.{c}.{tag}="
  | .tagEmpty => s!"{h}.{c}."
  | .twoParts => s!"{h}.{c}"
  | .fourParts => s!"{h}.{c}.{tag}.{tag}"
  | .emptyHeader => s!".{c}.{tag}"
  | .tagTruncated => s!"{h}.{c}.{String.ofList (tag.toList.take 42)}"
  | .swapParts => s!"{c}.{h}.{tag}"

/-- What EthLib says of a token, as the oracle names it. -/
def jwtVerdict (secret : ByteArray) (clock : Nat) (token : String) : String :=
  match Jwt.authenticate secret token with
  | .ok time => if Jwt.Json.within time clock then "ok" else "error iat"
  | .error (.secretLength _) => "error secret"
  | .error (.compact _) => "error compact"
  | .error .header => "error header"
  | .error (.algorithm _) => "error algorithm"
  | .error .critical => "error critical"
  | .error .claims => "error claims"
  | .error .signature => "error signature"
  | .error .serialization => "error serialization"

/-- A token passes exactly when the Engine profile accepts it, and fails for the model's reason.

The profile: a secret of 32 bytes, three parts in base64url without padding, the HS256 tag of the
first two, a header that names HS256 and no critical extension, and an `iat` that is a JSON number
within 60 seconds of the clock, both ends included. -/
def jwtChecks (oracle : Oracle) : Property IO := propertyM do
  let t ← forAll genTokenCase
  pure do
    let h := encodePart t.headerEncoding t.header
    let c := encodePart t.claimsEncoding t.claims
    let tag ← oracle.ask ["jwtmint", hex t.secret, textHex h, textHex c]
    let token := t.token tag
    let secret := if t.damage == .otherSecret then
      ⟨t.secret.data.modify 0 (· + 1)⟩ else t.secret
    annotate s!"token {token}"
    let expected ← oracle.ask ["jwtcheck", hex secret, toString t.clock, textHex token]
    jwtVerdict secret t.clock token === expected
    Jwt.check secret token t.clock === (expected == "ok")

/-- A token that EthLib builds is one that PyJWT verifies, with the issued-at time alone. -/
def jwtBuilds (oracle : Oracle) : Property IO := propertyM do
  let (secret, time) ← forAllWith (fun (s, t) => s!"{hex s} {t}")
    (Gen.zip (genBytes (.singleton 32)) genClock)
  pure do
    match Jwt.build secret time with
    | .ok token => (← oracle.ask ["jwtiat", hex secret, textHex token]) === toString time
    | .error _ => failWith "no token for a secret of 32 bytes"

end EngineProperty
