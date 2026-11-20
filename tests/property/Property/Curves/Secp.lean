import Property.Curves.Common
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Secp256r1
import EthLib.Cryptography.Exports.Secp256k1
import EthLib.Cryptography.Exports.Secp256r1

/-!
# secp256k1 and secp256r1 against libsecp256k1, OpenSSL and a model of SEC 1

Signing is RFC 6979, verification and recovery are SEC 1 v2 sections 4.1.4 and 4.1.6.

The inputs are valid signatures and keys, then changed at one place.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty

namespace K1

open Secp256k1

def n : Nat := Fn.modulus
def p : Nat := Fp.modulus

/-- A point in the oracle's form. -/
def coords : Point → Option (Nat × Nat)
  | .infinity => none
  | .affine x y => some (x.val, y.val)

def render (pt : Point) : String := showPoint (coords pt)

/-- The point of two coordinates, each reduced mod `p`. -/
def affine (x y : Nat) : Point := .affine (Fin.ofNat _ x) (Fin.ofNat _ y)

def fn (k : Nat) : Fn := Fin.ofNat _ k

/-- The signature of EthLib, as the oracle writes it. -/
def signText (d hash : Nat) : String :=
  match Ecdsa.sign (fn d) (vec32 hash) with
  | .ok (r, s, odd) => s!"{r.val} {s.val} {if odd then 1 else 0}"
  | .error _ => "error"

/-- Signing is RFC 6979 with the low-s rule, as libsecp256k1 and a model of the RFC sign. -/
def sign (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip ((· % n) <$> genNear n) (genNear n))
  -- The signature before the low-s rule, to see whether the rule changed it.
  let raw := Ecdsa.signWith (fn d) (Fin.ofNat _ hash) Rfc6979.MAX_NONCES
    (Ecdsa.nonceSeed (fn d) (vec32 hash))
  classify "the key is zero, refused" (d == 0)
  classify "the key is 1 or n - 1" (d == 1 || d + 1 == n)
  classify "the hash is n or more, so it is reduced" (hash ≥ n)
  classify "the hash is zero mod n" (hash % n == 0)
  classify "s was above n / 2 and is negated" (match raw with
    | .ok (_, s, _) => !Ecdsa.isLowS s.val
    | .error _ => false)
  classify "s was at most n / 2 and is kept" (match raw with
    | .ok (_, s, _) => Ecdsa.isLowS s.val
    | .error _ => false)
  classify "the recovery bit is 1" (match Ecdsa.sign (fn d) (vec32 hash) with
    | .ok (_, _, odd) => odd
    | .error _ => false)
  pure do
    signText d hash === (← oracle.ask ["k1sign", toString d, hexVec (vec32 hash)])

/-- One change to a valid signature, its hash or its key. -/
inductive Change where
  | none | highS | rPlusN | rZero | sZero | rIsN | sIsN | sPlusOne | rPlusOne
  | hashBit (bit : Nat) | otherKey | offCurve | negKey | infinity
  deriving Repr, BEq

def genChange : Gen Change :=
  Gen.frequency [
    (3, pure .none), (2, pure .highS), (1, pure .rPlusN), (1, pure .rZero), (1, pure .sZero),
    (1, pure .rIsN), (1, pure .sIsN), (1, pure .sPlusOne), (1, pure .rPlusOne),
    (2, .hashBit <$> Gen.nat (.constant 0 255)), (1, pure .otherKey), (1, pure .offCurve),
    (1, pure .negKey), (1, pure .infinity)]

/-- A signature with its hash and key, all as numbers. -/
structure Case where
  key : Option (Nat × Nat)
  hash : Nat
  r : Nat
  s : Nat
  deriving Repr

/-- Apply a change for a group of order `order` over a field of `prime` elements. -/
def Change.apply (order prime : Nat) (c : Case) : Change → Case
  | .none => c
  | .highS => { c with s := order - c.s }
  | .rPlusN => { c with r := c.r + order }
  | .rZero => { c with r := 0 }
  | .sZero => { c with s := 0 }
  | .rIsN => { c with r := order }
  | .sIsN => { c with s := order }
  | .sPlusOne => { c with s := c.s + 1 }
  | .rPlusOne => { c with r := c.r + 1 }
  | .hashBit bit => { c with hash := c.hash ^^^ (1 <<< bit) }
  | .otherKey => { c with key := c.key.map fun (x, y) => (y, x) }
  | .offCurve => { c with key := c.key.map fun (x, y) => (x, (y + 1) % prime) }
  | .negKey => { c with key := c.key.map fun (x, y) => (x, (prime - y) % prime) }
  | .infinity => { c with key := Option.none }

/-- The name of a change, for a label. -/
def Change.name : Change → String
  | .none => "nothing"
  | .highS => "s to n - s"
  | .rPlusN => "r to r + n"
  | .rZero => "r to zero"
  | .sZero => "s to zero"
  | .rIsN => "r to n"
  | .sIsN => "s to n"
  | .sPlusOne => "s to s + 1"
  | .rPlusOne => "r to r + 1"
  | .hashBit _ => "one bit of the hash"
  | .otherKey => "the key to another pair"
  | .offCurve => "the key off the curve"
  | .negKey => "the key to its negative"
  | .infinity => "the key to infinity"

/-- The first rule of SEC 1 v2 section 4.1.4 that refuses a case, for a label.

The order is that of EthLib's `verify`: `r`, then `s`, then the key, then the equation. -/
def refusal (order : Nat) (onCurve : Bool) (c : Case) : String :=
  if c.r == 0 then "r is zero"
  else if c.r == order then "r is n"
  else if c.r > order then "r is above n"
  else if c.s == 0 then "s is zero"
  else if c.s == order then "s is n"
  else if c.s > order then "s is above n"
  else if c.key.isNone then "the key is at infinity"
  else if !onCurve then "the key is off the curve"
  else "the equation fails"

def point (key : Option (Nat × Nat)) : Point :=
  match key with
  | none => .infinity
  | some (x, y) => affine x y

/-- A valid signature from EthLib's signer, or nothing when it refuses. -/
def signed (d hash : Nat) : Option Case :=
  match Ecdsa.sign (fn d) (vec32 hash), Point.mul (fn d) .generator with
  | .ok (r, s, _), .affine x y => some ⟨some (x.val, y.val), hash, r.val, s.val⟩
  | _, _ => none

/-- Verification is SEC 1 v2 section 4.1.4 on a signature changed at one place. -/
def verify (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let change ← forAll genChange
  let some valid := signed d hash | discard
  let c := change.apply n p valid
  pure do
    let got := Ecdsa.verify (point c.key) (vec32 c.hash) c.r c.s
    label s!"changed: {change.name}"
    classify "accepted" got
    classify "accepted with s above n / 2" (got && !Ecdsa.isLowS c.s)
    classify "the hash is n or more" (c.hash ≥ n)
    if !got then label s!"refused: {refusal n (point c.key).isOnCurve c}"
    (if got then "1" else "0") === (← oracle.ask
      ["k1verify", showPoint c.key, hexVec (vec32 c.hash), toString c.r, toString c.s])

/-- A signature whose `R` has `x >= n` verifies, since step 7 compares `x mod n` with `r`. -/
def verifyWrapped (oracle : Oracle) : Property IO := propertyM do
  let (u1, u2, x) ← forAll (Gen.zip (genScalar n) (Gen.zip (genScalar n) (genNear (p - n) 128)))
  pure do
    match words (← oracle.ask ["k1craft", toString u1, toString u2, toString x]) with
    | [key, e, r, s] =>
      let (some r, some s, some e) := (r.toNat?, s.toNat?, e.toNat?) | failWith "bad answer"
      let q := match key.splitOn "," with
        | [x, y] => affine x.toNat! y.toNat!
        | _ => .infinity
      annotate s!"key {key} e {e} r {r} s {s}"
      let expected ← oracle.ask ["k1verify", key, hexVec (vec32 e), toString r, toString s]
      expected === "1"
      ensure (Ecdsa.verify q (vec32 e) r s) "a signature with x_R >= n is refused"
      classify "r is 1, 2 or 3" (r ≤ 3)
      classify "r is in the upper half of [1, p - n)" (2 * r ≥ p - n)
      classify "s is above n / 2" (!Ecdsa.isLowS s)
      -- Recovery reads `r` as an `x`, so it finds another key or none, never this one.
      for odd in [0, 1] do
        let got := match Ecdsa.recover (vec32 e) r s odd with
          | .ok found => render found
          | .error _ => "error"
        got === (← oracle.ask ["k1recover", hexVec (vec32 e), toString r, toString s,
          toString odd.val])
        ensure (got != key) "recovery found a key whose R has x >= n"
        classify "recovery with x = r finds another key" (got != "error")
        classify "recovery with x = r finds no point" (got == "error")
    | other => failWith s!"bad answer {other}"

/-- The low-s rule of EIP-2 is `s <= n / 2` on the number. -/
def lowS : Property IO := pureIO do
  let s ← forAll (Gen.frequency [(1, Gen.element [(n - 1) / 2, (n + 1) / 2]), (5, genNear n)])
  classify "s is at most n / 2" (2 * s < n)
  classify "s is exactly (n - 1) / 2, the last low one" (2 * s + 1 == n)
  classify "s is exactly (n + 1) / 2, the first high one" (2 * s == n + 1)
  classify "s is n or more" (s ≥ n)
  Ecdsa.isLowS s === decide (2 * s < n)

/-- Recovery is SEC 1 v2 section 4.1.6 with the ids 0 and 1, as libsecp256k1 recovers. -/
def recover (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let change ← forAll (Gen.frequency [(4, genChange), (2, pure .none)])
  let flip ← forAll Gen.bool
  let some valid := signed d hash | discard
  let odd := match Ecdsa.sign (fn d) (vec32 hash) with
    | .ok (_, _, odd) => odd != flip
    | .error _ => flip
  let c := change.apply n p valid
  pure do
    let result := Ecdsa.recover (vec32 c.hash) c.r c.s (if odd then 1 else 0)
    let got := match result with
      | .ok q => render q
      | .error _ => "error"
    label s!"changed: {change.name}"
    classify "the recovery id is the other one" flip
    classify "the recovery id is 1" odd
    match result with
    | .ok _ =>
      classify "recovered the signer's key" (got == showPoint valid.key)
      classify "recovered another key" (got != showPoint valid.key)
    | .error e => label s!"refused: {ctorName e}"
    let expected ← oracle.ask ["k1recover", hexVec (vec32 c.hash), toString c.r, toString c.s,
      if odd then "1" else "0"]
    got === expected
    -- The unchanged signature with its own bit gives back the signer's key.
    if change == .none && !flip then got === showPoint valid.key

/-- Recovery at the edges of `r` and `s`, on any hash. -/
def recoverEdges (oracle : Oracle) : Property IO := propertyM do
  -- A signature whose key would be `O`: `R = k G`, any `s`, and the hash `e = s k`.
  --
  -- Then `s R - e G = O`, with the recovery id of `R`; the other id gives a key.
  let crafted : Gen (Nat × Nat × Nat × Bool) := do
    let (k, s) ← Gen.zip (genScalar n) (genScalar n)
    let other ← Gen.bool
    pure (match Point.mul (fn k) .generator with
      | .affine x y => (s * k % n, x.val, s, (y.val % 2 == 1) != other)
      | .infinity => (0, 1, 1, false))
  let edges : Gen (Nat × Nat × Nat × Bool) := do
    let (hash, r, s) ← Gen.zip (genNear n) (Gen.zip (genNear n) (genNear n))
    pure (hash, r, s, ← Gen.bool)
  let (hash, r, s, odd) ← forAll (Gen.frequency [(4, edges), (1, crafted)])
  pure do
    let result := Ecdsa.recover (vec32 hash) r s (if odd then 1 else 0)
    let got := match result with
      | .ok q => render q
      | .error _ => "error"
    label s!"r is {rangeClass n r}"
    label s!"s is {rangeClass n s}"
    classify "r is in [n, p), an x that recovery never tries" (n ≤ r && r < p)
    match result with
    | .ok _ => label "recovered a key"
    | .error e => label s!"refused: {ctorName e}"
    got === (← oracle.ask ["k1recover", hexVec (vec32 hash), toString r, toString s,
      if odd then "1" else "0"])

/-- An encoding of a point, valid or changed at one place.

A valid point comes in each of its three forms, so that each prefix decodes often.

Each refusal of the decoder has a shape of its own here. -/
def genEncoding : Gen ByteArray := do
  let d ← genScalar n
  let (x, y) := match Point.mul (fn d) .generator with
    | .affine x y => (x.val, y.val)
    | .infinity => (0, 0)
  let parity : UInt8 := if y % 2 == 0 then 2 else 3
  let tagged (tag : UInt8) (body : ByteArray) : ByteArray := ByteArray.mk #[tag] ++ body
  let anyX ← genNear p
  let big ← (p + ·) <$> Gen.nat (.linear 0 3)
  let tag ← Gen.frequency [(2, Gen.integral (.constant 0 7)), (1, genByte)]
  Gen.frequency [
    -- The three valid forms: the parity may be the other one, which is the opposite point.
    (3, pure (tagged parity (beBytes 32 x))),
    (2, pure (tagged (5 - parity) (beBytes 32 x))),
    (4, pure (tagged 4 (beBytes 32 x ++ beBytes 32 y))),
    -- Compressed, with an `x` that may have no point, or is `p` or more.
    (3, pure (tagged parity (beBytes 32 anyX))),
    (1, pure (tagged parity (beBytes 32 big))),
    -- Uncompressed, off the curve or with a coordinate of `p` or more.
    (2, pure (tagged 4 (beBytes 32 x ++ beBytes 32 ((y + 1) % p)))),
    (1, pure (tagged 4 (beBytes 32 anyX ++ beBytes 32 y))),
    (1, pure (tagged 4 (beBytes 32 big ++ beBytes 32 y))),
    (1, pure (tagged 4 (beBytes 32 x ++ beBytes 32 big))),
    -- The point at infinity, which is no public key.
    (2, pure (ByteArray.mk #[0])),
    -- A prefix that does not fit the length, and the hybrid prefixes 06 and 07.
    (1, pure (tagged 4 (beBytes 32 x))),
    (1, pure (tagged parity (beBytes 32 x ++ beBytes 32 y))),
    (2, pure (tagged tag (beBytes 32 x))),
    (2, pure (tagged tag (beBytes 32 x ++ beBytes 32 y))),
    (1, pure (tagged (6 + parity % 2) (beBytes 32 x ++ beBytes 32 y))),
    -- Another length.
    (1, pure ByteArray.empty),
    (1, pure (tagged parity (beBytes 31 x))),
    (1, pure (tagged parity (beBytes 33 x))),
    (1, pure (tagged 4 (beBytes 32 x ++ beBytes 31 y))),
    (1, pure (tagged 4 (beBytes 32 x ++ beBytes 33 y))),
    (1, pure (beBytes 32 x))]

/-- The decoder accepts the two encodings of SEC 1 v2 section 2.3.4 and nothing else. -/
def decode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex genEncoding
  pure do
    let result := Point.decode bytes
    let got := match result with
      | .ok q => render q
      | .error _ => "error"
    let tag := if bytes.size == 0 then "none" else toString bytes[0]!
    match result with
    | .ok _ => label s!"decoded with prefix {tag}"
    | .error e => label s!"refused: {ctorName e}"
    classify "33 bytes" (bytes.size == 33)
    classify "65 bytes" (bytes.size == 65)
    classify "another length" (bytes.size != 33 && bytes.size != 65)
    got === (← oracle.ask ["k1decode", hex bytes])

/-- Both encodings of a point read back as that point, in libsecp256k1 and in EthLib. -/
def encode (oracle : Oracle) : Property IO := propertyM do
  let d ← forAll (genScalar n)
  let q := Point.mul (fn d) .generator
  pure do
    for bytes in [q.encodeCompressed, q.encodeUncompressed] do
      render q === (← oracle.ask ["k1decode", hex bytes])
      tripping q (fun _ => bytes) (fun b => (Point.decode b).toOption)

/-- A scalar for the group law: the edges of `[0, n)` and the rest. -/
def genGroupScalar : Gen Nat := (· % n) <$> genNear n

/-- `k G`, `k P` with 256 bits of `k`, the sum and `k P + l Q` are those of the model. -/
def group (oracle : Oracle) : Property IO := propertyM do
  let (k, l) ← forAll (Gen.zip genGroupScalar genGroupScalar)
  -- The second point is often the first or its negative: the doubling and cancelling branches.
  let m ← forAll (Gen.frequency [(2, pure k), (2, pure ((n - k) % n)), (3, genGroupScalar)])
  let wide ← forAll (genNear n)
  classify "P + Q with P = Q, a doubling" (k == m && k != 0)
  classify "P + Q with P = -Q, the point at infinity" ((k + m) % n == 0 && k != 0)
  classify "P + Q with two other points" (k != m && (k + m) % n != 0 && k != 0 && m != 0)
  classify "P is at infinity" (k == 0)
  classify "Q is at infinity" (m == 0)
  classify "the scalar is 1" (k == 1)
  classify "the scalar is n - 1" (k + 1 == n)
  classify "the wide scalar is n" (wide == n)
  classify "the wide scalar is above n" (wide > n)
  classify "the wide scalar is zero" (wide == 0)
  classify "k P + l Q is at infinity" ((l * k + k * m) % n == 0)
  pure do
    let g := render Point.generator
    let pk := Point.mul (fn k) .generator
    let pm := Point.mul (fn m) .generator
    render pk === (← oracle.ask ["mul", "k1", toString k, g])
    render (pk + pm) === (← oracle.ask ["add", "k1", render pk, render pm])
    render (Point.mulAdd (fn l) pk (fn k) pm) === (← oracle.ask
      ["muladd", "k1", toString l, render pk, toString k, render pm])
    render (Point.mulBits 256 wide pm) === (← oracle.ask ["mul", "k1", toString wide, render pm])
    render (Point.ofJacobian (Point.toJacobian pk)) === render pk
    ensure (pk.isOnCurve && (pk + pm).isOnCurve) "a point left the curve"
    ensure ((pk + (-pk)) == .infinity) "P + (-P) is not O"

/-- ECDH gives the `x` of `d Q`, and refuses a key off the curve and the point at infinity. -/
def ecdh (oracle : Oracle) : Property IO := propertyM do
  let (d, k) ← forAll (Gen.zip genGroupScalar (genScalar n))
  let bad ← forAll (Gen.frequency [(5, pure 0), (1, pure 1), (1, pure 2)])
  pure do
    let q := Point.mul (fn k) .generator
    let q := match bad, q with
      | 1, .affine x y => Point.affine x (y + 1)
      | 2, _ => .infinity
      | _, q => q
    let expected ← if bad != 0 then pure "inf" else oracle.ask ["mul", "k1", toString d, render q]
    let result := Secp256k1.ecdh (fn d) q
    let got := match result with
      | .ok secret => s!"{beNat ⟨secret.toArray⟩}"
      | .error _ => "inf"
    match result with
    | .ok _ => label "a shared secret"
    | .error e =>
      label s!"refused: {ctorName e}{if bad == 0 then ", by a zero key" else ", by the public key"}"
    got === ((expected.splitOn ",").headD "inf")

/-- The address is the last 20 bytes of the Keccak-256 of the key, as eth-keys computes it. -/
def address (oracle : Oracle) : Property IO := propertyM do
  let d ← forAll genGroupScalar
  classify "the key is zero, with no address" (d == 0)
  classify "the key is 1 or n - 1" (d == 1 || d + 1 == n)
  pure do
    match Point.mul (fn d) .generator with
    | .affine x y =>
      let expected ← oracle.ask ["k1address", s!"{x.val},{y.val}"]
      hexVec (Secp256k1.address x y) === expected
      (addressOfPrivateKey (fn d)).map hexVec === some expected
    | .infinity => (addressOfPrivateKey (fn d)).map hexVec === none

/-- The field kernels are arithmetic mod `p` and mod `n` on `Nat`. -/
def field : Property IO := pureIO do
  let (a, e) ← forAll (Gen.zip (genNear p) (genNear p))
  let x : Fp := Fin.ofNat _ a
  classify "a is zero mod p" (a % p == 0)
  classify "a is p or more" (a ≥ p)
  classify "a is a square mod p" (modPow p a ((p - 1) / 2) == 1)
  classify "a is not a square mod p" (modPow p a ((p - 1) / 2) == p - 1)
  classify "the exponent is zero" (e == 0)
  (x.pow e).val === modPow p a e
  (Fn.pow (Fin.ofNat _ a) e).val === modPow n a e
  ensure (a % p == 0 || (x.inv * x).val == 1) "the inverse mod p is wrong"
  (Fp.inv 0).val === 0
  let y : Fn := Fin.ofNat _ a
  ensure (a % n == 0 || (y.inv * y).val == 1) "the inverse mod n is wrong"
  -- Euler's criterion decides whether a root exists.
  let square := (x.pow ((p - 1) / 2)).val != p - 1
  match x.sqrt with
  | some root => ensure (square && (root * root) == x) "a root that does not square back"
  | none => ensure (!square) "a square without a root"
  -- A power is the product of its two halves.
  let (e1, e2) := (e / 2, e - e / 2)
  (x.pow e).val === (x.pow e1 * x.pow e2).val

/-- Bytes of a length that is right in most cases: one byte short, one long, or none. -/
def genSized (right : Nat) (value : Nat) : Gen ByteArray :=
  Gen.frequency [(16, pure (beBytes right value)), (1, pure (beBytes (right - 1) value)),
    (1, pure (beBytes (right + 1) value)), (1, pure ByteArray.empty)]

/-- The answer of an export, for a comparison: its value, or `error`. -/
def exported {α : Type} (shown : α → String) (result : Except (UInt32 × String) α) : String :=
  match result with
  | .ok value => shown value
  | .error _ => "error"

/-- The operations on bytes that the bindings call are the functions under them.

Each refuses a hash, a signature or a key of another length, and a recovery id above 1.

A private key of `n` or more is refused and not reduced. -/
def exports (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (Gen.frequency [(4, genScalar n), (2, genNear n)]) (genNear n))
  let change ← forAll (Gen.frequency [(3, pure Change.none), (2, genChange)])
  let recid ← forAll (Gen.frequency [(6, Gen.element [(0 : UInt8), 1]),
    (2, Gen.element [2, 3, 27, 28, 255])])
  let compressed ← forAll Gen.bool
  let other ← forAllWith hex genEncoding
  -- A valid signature of a key in range, then one change; the key `d` itself may be out of it.
  let signer := d % (n - 1) + 1
  let some valid := signed signer hash | discard
  let c := change.apply n p valid
  let (hashBytes, sigR, sigS) ← forAllWith (fun (a, b, c) => s!"{hex a} {hex b} {hex c}")
    (Gen.zip (genSized 32 c.hash) (Gen.zip (genSized 32 (c.r % 2 ^ 256))
      (pure (beBytes 32 (c.s % 2 ^ 256)))))
  let keyBytes ← forAllWith hex (genSized 32 d)
  pure do
    let sig := sigR ++ sigS
    let signerKey := Point.mul (fn signer) .generator
    let pk := match change with
      | .offCurve | .otherKey | .infinity => other
      | _ => if compressed then signerKey.encodeCompressed else signerKey.encodeUncompressed
    let sizes := hashBytes.size == 32 && sig.size == 64
    let (r, s) := (beNat (sig.extract 0 32), beNat (sig.extract 32 64))
    let e := vec32 (beNat hashBytes)
    -- Verification.
    let decoded ← oracle.ask ["k1decode", hex pk]
    let wantVerify ← if decoded == "error" || !sizes then pure "error"
      else oracle.ask ["k1verify", decoded, hexVec e, toString r, toString s]
    let gotVerify := exported (fun (b : UInt8) => toString b.toNat)
      (Exports.verifyExport pk hashBytes sig)
    gotVerify === wantVerify
    label s!"verify: {gotVerify}"
    -- The low-s rule.
    exported (fun (b : UInt8) => toString b.toNat) (Exports.isLowSExport sig) ===
      (if sig.size == 64 then (if 2 * s < n then "1" else "0") else "error")
    -- Recovery.
    let point ← if !sizes || recid ≥ 2 then pure "error"
      else oracle.ask ["k1recover", hexVec e, toString r, toString s, toString recid.toNat]
    let wantRecover := match point.splitOn "," with
      | [x, y] => hex (ByteArray.mk #[4] ++ beBytes 32 x.toNat! ++ beBytes 32 y.toNat!)
      | _ => "error"
    let gotRecover := exported hex (Exports.recoverExport hashBytes sig recid)
    gotRecover === wantRecover
    classify "recover: a key" (gotRecover != "error")
    classify "recover: refused by a recovery id above 1" (sizes && recid ≥ 2)
    classify "refused by the length of the hash" (hashBytes.size != 32)
    classify "refused by the length of the signature" (sig.size != 64)
    -- Signing, the shared secret and the address, with the key as bytes.
    let keyOk := keyBytes.size == 32 && 0 < d && d < n
    classify "the key is n or more, refused" (keyBytes.size == 32 && d ≥ n)
    classify "the key is zero, refused" (keyBytes.size == 32 && d == 0)
    classify "the key has another length, refused" (keyBytes.size != 32)
    let wantSign ← if !keyOk || hashBytes.size != 32 then pure "error" else do
      match words (← oracle.ask ["k1sign", toString d, hexVec e]) with
      | [r, s, v] => pure (hex (beBytes 32 r.toNat! ++ beBytes 32 s.toNat! ++ beBytes 1 v.toNat!))
      | _ => pure "error"
    let gotSign := exported hex (Exports.signExport keyBytes hashBytes)
    gotSign === wantSign
    classify "sign: a signature" (gotSign != "error")
    let wantSecret ← if !keyOk || decoded == "error" then pure "error" else do
      let product ← oracle.ask ["mul", "k1", toString d, decoded]
      pure (match product.splitOn "," with
        | [x, _] => hex (beBytes 32 x.toNat!)
        | _ => "error")
    exported hex (Exports.ecdhExport keyBytes pk) === wantSecret
    classify "ecdh: a secret" (wantSecret != "error")
    let wantAddress ← if !keyOk then pure "error" else do
      oracle.ask ["k1address", ← oracle.ask ["mul", "k1", toString d, render Point.generator]]
    exported hex (Exports.addressExport keyBytes) === wantAddress

end K1

namespace R1

open Secp256r1

def n : Nat := Fn.modulus
def p : Nat := Fp.modulus

def coords : Point → Option (Nat × Nat)
  | .infinity => none
  | .affine x y => some (x.val, y.val)

def render (pt : Point) : String := showPoint (coords pt)

def fn (k : Nat) : Fn := Fin.ofNat _ k

def point (key : Option (Nat × Nat)) : Point :=
  match key with
  | none => .infinity
  | some (x, y) => .affine (Fin.ofNat _ x) (Fin.ofNat _ y)

/-- Signing is RFC 6979, as OpenSSL's deterministic ECDSA and a model of the RFC sign. -/
def sign (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip ((· % n) <$> genNear n) (genNear n))
  classify "the key is zero, refused" (d == 0)
  classify "the key is 1 or n - 1" (d == 1 || d + 1 == n)
  classify "the hash is n or more, so it is reduced" (hash ≥ n)
  classify "the hash is zero mod n" (hash % n == 0)
  classify "s is above n / 2, and is kept" (match Ecdsa.sign (fn d) (vec32 hash) with
    | some (_, s) => 2 * s.val > n
    | none => false)
  pure do
    let got := match Ecdsa.sign (fn d) (vec32 hash) with
      | some (r, s) => s!"{r.val} {s.val}"
      | none => "error"
    got === (← oracle.ask ["r1sign", toString d, hexVec (vec32 hash)])

/-- Verification is SEC 1 v2 section 4.1.4, as EIP-7951 states it, on a changed signature. -/
def verify (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let change ← forAll K1.genChange
  let some (r, s) := Ecdsa.sign (fn d) (vec32 hash) | discard
  let key := coords (Point.mul (fn d) .generator)
  let c := change.apply n p ⟨key, hash, r.val, s.val⟩
  pure do
    let got := Secp256r1.verify (point c.key) c.hash c.r c.s
    label s!"changed: {change.name}"
    classify "accepted" got
    classify "accepted with s above n / 2" (got && 2 * c.s > n)
    classify "the hash is n or more" (c.hash ≥ n)
    if !got then label s!"refused: {K1.refusal n (point c.key).isOnCurve c}"
    (if got then "1" else "0") === (← oracle.ask
      ["r1verify", showPoint c.key, hexVec (vec32 c.hash), toString c.r, toString c.s])

/-- A signature whose `R` has `x >= n` verifies: EIP-7951 compares `x mod n` with `r`.

`p - n` is near `2^128` on P-256, so such an `R` never comes from a signer; the oracle crafts it. -/
def verifyWrapped (oracle : Oracle) : Property IO := propertyM do
  let (u1, u2, x) ← forAll (Gen.zip (genScalar n) (Gen.zip (genScalar n) (genNear (p - n) 128)))
  pure do
    match words (← oracle.ask ["r1craft", toString u1, toString u2, toString x]) with
    | [key, e, r, s] =>
      let (some r, some s, some e) := (r.toNat?, s.toNat?, e.toNat?) | failWith "bad answer"
      let q := match key.splitOn "," with
        | [x, y] => point (some (x.toNat!, y.toNat!))
        | _ => .infinity
      annotate s!"key {key} e {e} r {r} s {s}"
      ensure (r < p - n) "the crafted r is not below p - n"
      (← oracle.ask ["r1verify", key, hexVec (vec32 e), toString r, toString s]) === "1"
      ensure (Secp256r1.verify q e r s) "a signature with x_R >= n is refused"
      classify "r is 1, 2 or 3" (r ≤ 3)
      classify "r is in the upper half of [1, p - n)" (2 * r ≥ p - n)
      classify "s is above n / 2" (2 * s > n)
      -- The same signature with `r + n`, the abscissa itself, is out of range.
      ensure (!Secp256r1.verify q e (r + n) s) "r = x_R, which is n or more, is accepted"
    | other => failWith s!"bad answer {other}"

/-- Verification on any numbers at the edges, with a key of the curve. -/
def verifyEdges (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let (r, s) ← forAll (Gen.zip (genNear n) (genNear n))
  let key := coords (Point.mul (fn d) .generator)
  pure do
    let got := Secp256r1.verify (point key) hash r s
    label s!"r is {rangeClass n r}"
    label s!"s is {rangeClass n s}"
    classify "accepted" got
    (if got then "1" else "0") === (← oracle.ask
      ["r1verify", showPoint key, hexVec (vec32 hash), toString r, toString s])

/-- The decoder accepts `04 | x | y` of a point of the curve and nothing else. -/
def decode (oracle : Oracle) : Property IO := propertyM do
  let d ← forAll (genScalar n)
  let (x, y) := (coords (Point.mul (fn d) .generator)).getD (0, 0)
  let x ← forAll (Gen.frequency [(6, pure x), (1, genNear p), (1, (p + ·)
      <$> Gen.nat (.linear 0 3))])
  let y ← forAll (Gen.frequency [(6, pure y), (1, pure (p - y)), (1, genNear p),
    (1, (p + ·) <$> Gen.nat (.linear 0 3))])
  let tag ← forAll (Gen.frequency [(6, pure 4), (2, Gen.integral (.constant 0 7)), (1, genByte)])
  let body ← forAllWith hex (Gen.frequency [
    (8, pure (beBytes 32 x ++ beBytes 32 y)), (1, pure (beBytes 32 x)),
    (1, pure (beBytes 32 x ++ beBytes 31 y)), (1, pure (beBytes 32 x ++ beBytes 33 y))])
  pure do
    let bytes := ByteArray.mk #[tag] ++ body
    let got := match decodeUncompressed bytes.toList with
      | some q => render q
      | none => "error"
    classify "decoded" (got != "error")
    classify "refused: the prefix is not 04" (tag != 4)
    classify "refused: the prefix is 02 or 03, a compressed form" (tag == 2 || tag == 3)
    classify "refused: another length" (bytes.size != 65)
    classify "refused: x is p or more" (tag == 4 && bytes.size == 65 && x ≥ p)
    classify "refused: y is p or more" (tag == 4 && bytes.size == 65 && x < p && y ≥ p)
    classify "refused: off the curve" (tag == 4 && bytes.size == 65 && x < p && y < p &&
      got == "error")
    got === (← oracle.ask ["r1decode", hex bytes])

/-- `k G`, the sum and `k P + l Q` are those of the model, with `a = -3`. -/
def group (oracle : Oracle) : Property IO := propertyM do
  let scalar := (· % n) <$> genNear n
  let (k, l) ← forAll (Gen.zip scalar scalar)
  let m ← forAll (Gen.frequency [(2, pure k), (2, pure ((n - k) % n)), (3, scalar)])
  let wide ← forAll (genNear n)
  classify "P + Q with P = Q, a doubling" (k == m && k != 0)
  classify "P + Q with P = -Q, the point at infinity" ((k + m) % n == 0 && k != 0)
  classify "P + Q with two other points" (k != m && (k + m) % n != 0 && k != 0 && m != 0)
  classify "P is at infinity" (k == 0)
  classify "Q is at infinity" (m == 0)
  classify "the scalar is 1" (k == 1)
  classify "the scalar is n - 1" (k + 1 == n)
  classify "the wide scalar is n" (wide == n)
  classify "the wide scalar is above n" (wide > n)
  classify "the wide scalar is zero" (wide == 0)
  classify "k P + l Q is at infinity" ((l * k + k * m) % n == 0)
  pure do
    let pk := Point.mul (fn k) .generator
    let pm := Point.mul (fn m) .generator
    render pk === (← oracle.ask ["mul", "r1", toString k, render Point.generator])
    render (pk + pm) === (← oracle.ask ["add", "r1", render pk, render pm])
    render (Point.mulAdd (fn l) pk (fn k) pm) === (← oracle.ask
      ["muladd", "r1", toString l, render pk, toString k, render pm])
    render (Point.mulBits 256 wide pm) === (← oracle.ask ["mul", "r1", toString wide, render pm])
    ensure (pk.isOnCurve && (pk + pm).isOnCurve) "a point left the curve"
    match decodeUncompressed (match pk with
      | .affine x y => encodeUncompressed x y
      | .infinity => []) with
    | some q => q === pk
    | none => pk === .infinity

/-- The verification on bytes that the bindings call is the function under it.

A key is `x` then `y`, 32 bytes each and below `p`; a hash is 32 bytes and a signature 64. -/
def exports (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let change ← forAll (Gen.frequency [(3, pure K1.Change.none), (2, K1.genChange)])
  let some (r, s) := Ecdsa.sign (fn d) (vec32 hash) | discard
  let key := coords (Point.mul (fn d) .generator)
  let c := change.apply n p ⟨key, hash, r.val, s.val⟩
  let (x, y) := c.key.getD (0, 0)
  let big ← forAll (Gen.frequency [(8, pure 0), (1, pure 1), (1, pure 2)])
  let (hashBytes, sigR, keyX) ← forAllWith (fun (a, b, c) => s!"{hex a} {hex b} {hex c}")
    (Gen.zip (K1.genSized 32 c.hash) (Gen.zip (K1.genSized 32 (c.r % 2 ^ 256))
      (K1.genSized 32 (if big == 1 then p else x))))
  pure do
    let sig := sigR ++ beBytes 32 (c.s % 2 ^ 256)
    let keyBytes := keyX ++ beBytes 32 (if big == 2 then p + 1 else y)
    let sizes := hashBytes.size == 32 && sig.size == 64 && keyBytes.size == 64
    let (kx, ky) := (beNat (keyBytes.extract 0 32), beNat (keyBytes.extract 32 64))
    let want ← if !sizes || kx ≥ p || ky ≥ p then pure "error"
      else oracle.ask ["r1verify", s!"{kx},{ky}", hex hashBytes,
        toString (beNat (sig.extract 0 32)), toString (beNat (sig.extract 32 64))]
    let got := K1.exported (fun (b : UInt8) => toString b.toNat)
      (Exports.verifyExport keyBytes hashBytes sig)
    label s!"verify: {got}"
    classify "refused by a coordinate of p or more" (sizes && (kx ≥ p || ky ≥ p))
    classify "refused by a length" (!sizes)
    got === want

end R1

end CurvesProperty
