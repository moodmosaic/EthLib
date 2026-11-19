import Property.Curves.Common
import EthLib.Cryptography.Secp256k1
import EthLib.Cryptography.Secp256r1

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
    | other => failWith s!"bad answer {other}"

/-- The low-s rule of EIP-2 is `s <= n / 2` on the number. -/
def lowS : Property IO := pureIO do
  let s ← forAll (genNear n)
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
    let got := match Ecdsa.recover (vec32 c.hash) c.r c.s (if odd then 1 else 0) with
      | .ok q => render q
      | .error _ => "error"
    let expected ← oracle.ask ["k1recover", hexVec (vec32 c.hash), toString c.r, toString c.s,
      if odd then "1" else "0"]
    got === expected
    -- The unchanged signature with its own bit gives back the signer's key.
    if change == .none && !flip then got === showPoint valid.key

/-- Recovery at the edges of `r` and `s`, on any hash. -/
def recoverEdges (oracle : Oracle) : Property IO := propertyM do
  let (hash, r, s) ← forAll (Gen.zip (genNear n) (Gen.zip (genNear n) (genNear n)))
  let odd ← forAll Gen.bool
  pure do
    let got := match Ecdsa.recover (vec32 hash) r s (if odd then 1 else 0) with
      | .ok q => render q
      | .error _ => "error"
    got === (← oracle.ask ["k1recover", hexVec (vec32 hash), toString r, toString s,
      if odd then "1" else "0"])

/-- An encoding of a point, valid or changed at one place. -/
def genEncoding : Gen ByteArray := do
  let d ← genScalar n
  let (x, y) := match Point.mul (fn d) .generator with
    | .affine x y => (x.val, y.val)
    | .infinity => (0, 0)
  let x ← Gen.frequency [(6, pure x), (1, genNear p), (1, (p + ·) <$> Gen.nat (.linear 0 3))]
  let y ← Gen.frequency [(6, pure y), (1, pure (p - y)), (1, genNear p)]
  let tag ← Gen.frequency [(6, Gen.element [2, 3, 4]), (2, Gen.integral (.constant 0 7)),
    (1, genByte)]
  let body ← Gen.frequency [
    (4, pure (beBytes 32 x)), (4, pure (beBytes 32 x ++ beBytes 32 y)),
    (1, pure ByteArray.empty), (1, pure (beBytes 31 x)), (1, pure (beBytes 33 x)),
    (1, pure (beBytes 32 x ++ beBytes 31 y)), (1, pure (beBytes 32 x ++ beBytes 33 y))]
  Gen.frequency [(9, pure (ByteArray.mk #[tag] ++ body)), (1, pure body)]

/-- The decoder accepts the two encodings of SEC 1 v2 section 2.3.4 and nothing else. -/
def decode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex genEncoding
  pure do
    let got := match Point.decode bytes with
      | .ok q => render q
      | .error _ => "error"
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
    let got := match Secp256k1.ecdh (fn d) q with
      | .ok secret => s!"{beNat ⟨secret.toArray⟩}"
      | .error _ => "inf"
    got === ((expected.splitOn ",").headD "inf")

/-- The address is the last 20 bytes of the Keccak-256 of the key, as eth-keys computes it. -/
def address (oracle : Oracle) : Property IO := propertyM do
  let d ← forAll genGroupScalar
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
    (if got then "1" else "0") === (← oracle.ask
      ["r1verify", showPoint c.key, hexVec (vec32 c.hash), toString c.r, toString c.s])

/-- Verification on any numbers at the edges, with a key of the curve. -/
def verifyEdges (oracle : Oracle) : Property IO := propertyM do
  let (d, hash) ← forAll (Gen.zip (genScalar n) (genNear n))
  let (r, s) ← forAll (Gen.zip (genNear n) (genNear n))
  let key := coords (Point.mul (fn d) .generator)
  pure do
    let got := Secp256r1.verify (point key) hash r s
    (if got then "1" else "0") === (← oracle.ask
      ["r1verify", showPoint key, hexVec (vec32 hash), toString r, toString s])

/-- The decoder accepts `04 | x | y` of a point of the curve and nothing else. -/
def decode (oracle : Oracle) : Property IO := propertyM do
  let d ← forAll (genScalar n)
  let (x, y) := (coords (Point.mul (fn d) .generator)).getD (0, 0)
  let x ← forAll (Gen.frequency [(6, pure x), (1, genNear p), (1, (p + ·)
      <$> Gen.nat (.linear 0 3))])
  let y ← forAll (Gen.frequency [(6, pure y), (1, pure (p - y)), (1, genNear p)])
  let tag ← forAll (Gen.frequency [(6, pure 4), (2, Gen.integral (.constant 0 7)), (1, genByte)])
  let body ← forAllWith hex (Gen.frequency [
    (8, pure (beBytes 32 x ++ beBytes 32 y)), (1, pure (beBytes 32 x)),
    (1, pure (beBytes 32 x ++ beBytes 31 y)), (1, pure (beBytes 32 x ++ beBytes 33 y))])
  pure do
    let bytes := ByteArray.mk #[tag] ++ body
    let got := match decodeUncompressed bytes.toList with
      | some q => render q
      | none => "error"
    got === (← oracle.ask ["r1decode", hex bytes])

/-- `k G`, the sum and `k P + l Q` are those of the model, with `a = -3`. -/
def group (oracle : Oracle) : Property IO := propertyM do
  let scalar := (· % n) <$> genNear n
  let (k, l) ← forAll (Gen.zip scalar scalar)
  let m ← forAll (Gen.frequency [(2, pure k), (2, pure ((n - k) % n)), (3, scalar)])
  let wide ← forAll (genNear n)
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

end R1

end CurvesProperty
