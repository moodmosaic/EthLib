import Property.Curves.Common
import EthLib.Cryptography.Bls

/-!
# BLS12-381 against py_ecc, arkworks and milagro

The encodings are the Zcash ones of the BLS signature draft, section 2.5.

The signatures are the proof-of-possession scheme of that draft, and the wrappers of Ethereum.

The inputs are valid points, keys and signatures, then changed at one place.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace CurvesProperty.Bls12

open Bls

def r : Nat := Fr.modulus
def p : Nat := Fp.modulus

def render1 (pt : G1) : String :=
  if pt.isInfinity then "inf" else
    let (x, y) := pt.toAffine
    s!"{x.val},{y.val}"

def render2 (pt : G2) : String :=
  if pt.isInfinity then "inf" else
    let (x, y) := pt.toAffine
    s!"{x.c0.val},{x.c1.val},{y.c0.val},{y.c1.val}"

def vec (n : Nat) (bytes : ByteArray) : Vector UInt8 n :=
  Vector.ofFn fun i => bytes[i.val]!

/-- A list in the oracle's form. -/
def listWord (items : List String) : String :=
  if items.isEmpty then "[]" else ";".intercalate items

/-! ## Fields -/

/-- `Fr` and `Fp` in Montgomery limbs are the integers mod `r` and mod `p`. -/
def fields : Property IO := pureIO do
  let (a, b) ← forAll (Gen.zip (genNear r) (genNear r))
  let (x, y) := (Fr.ofNat a, Fr.ofNat b)
  classify "Fr: 32 bytes of a number below r, decoded" (a < r)
  classify "Fr: 32 bytes of exactly r, refused" (a == r)
  classify "Fr: 32 bytes of a number above r, refused" (a > r)
  classify "Fr: zero" (a % r == 0)
  classify "Fr: a division by zero" (b % r == 0)
  x.val === a % r
  (x + y).val === (a + b) % r
  (x - y).val === (a % r + r - b % r) % r
  (x * y).val === a * b % r
  (-x).val === (r - a % r) % r
  (x.powNat b).val === modPow r a b
  (x.inverse).val === modPow r a (r - 2)
  (x / y).val === a % r * modPow r b (r - 2) % r
  beNat x.toBytesBE === a % r
  x.toBytesBE.size === 32
  -- The decoder takes exactly 32 bytes of a number below `r`.
  (Fr.fromBytesBE (beBytes 32 a)).toOption.map (·.val) === (if a < r then some a else none)
  (Fr.fromBytesBE (beBytes 31 (a % 2 ^ 248))).toOption.map (·.val) === none
  (Fr.fromBytesBE (beBytes 33 a)).toOption.map (·.val) === none
  let (c, d) ← forAll (Gen.zip (genNear p 384) (genNear p 384))
  let (u, v) := (Fp.ofNat c, Fp.ofNat d)
  classify "Fp: 48 bytes of a number below p, decoded" (c < p)
  classify "Fp: 48 bytes of exactly p, refused" (c == p)
  classify "Fp: 48 bytes of a number above p, refused" (c > p)
  classify "Fp: a square" (modPow p c ((p - 1) / 2) == 1)
  classify "Fp: not a square" (modPow p c ((p - 1) / 2) == p - 1)
  classify "Fp: zero" (c % p == 0)
  u.val === c % p
  (u + v).val === (c + d) % p
  (u - v).val === (c % p + p - d % p) % p
  (u * v).val === c * d % p
  (-u).val === (p - c % p) % p
  (u.powNat d).val === modPow p c d
  u.inverse.val === modPow p c (p - 2)
  beNat u.toBytesBE === c % p
  (Fp.fromBytesBE (beBytes 48 c)).toOption.map (·.val) === (if c < p then some c else none)
  (Fp.fromBytesBE (beBytes 47 (c % 2 ^ 376))).toOption.map (·.val) === none
  -- Euler's criterion decides whether a root exists.
  let square := modPow p c ((p - 1) / 2) != p - 1
  match u.sqrt with
  | .ok root => ensure (square && (root * root).val == c % p) "a root that does not square back"
  | .error _ => ensure (!square) "a square without a root"

/-- The inverses of a list, zeros included, are the inverses one by one. -/
def batchInverse : Property IO := pureIO do
  let xs ← forAll (Gen.list (.linear 0 12) (Gen.frequency [(1, pure 0), (1, pure r),
      (5, genNear r)]))
  let frs := (xs.map Fr.ofNat).toArray
  classify "no element" xs.isEmpty
  classify "one element" (xs.length == 1)
  classify "a zero among the elements" (xs.any (· % r == 0))
  classify "a zero first" (xs.head?.any (· % r == 0))
  classify "a zero last" (xs.getLast?.any (· % r == 0))
  classify "only zeros" (!xs.isEmpty && xs.all (· % r == 0))
  (Fr.batchInverse frs).toList.map (·.val) === xs.map fun a => modPow r a (r - 2)

/-- A square root in `Fp2` squares back, and fails exactly on a non-square. -/
def sqrt2 : Property IO := pureIO do
  let (a, b) ← forAll (Gen.zip (genNear p 384) (Gen.frequency [(1, pure 0), (4, genNear p 384)]))
  let squareIt ← forAll Gen.bool
  let z : Fp2 := ⟨Fp.ofNat a, Fp.ofNat b⟩
  let z := if squareIt then z * z else z
  -- An element of `Fp2` is a square exactly when its norm is one in `Fp`.
  let norm := (z.c0 * z.c0 + z.c1 * z.c1).val
  let square := modPow p norm ((p - 1) / 2) != p - 1
  let euler (x : Nat) : Bool := modPow p x ((p - 1) / 2) != p - 1
  classify "real, a square of Fp: the root is real" (z.c1.val == 0 && euler z.c0.val)
  classify "real, not a square of Fp: the root is imaginary" (z.c1.val == 0 && !euler z.c0.val)
  classify "zero" (z.c0.val == 0 && z.c1.val == 0)
  classify "not real, not a square: refused" (z.c1.val != 0 && !square)
  -- The half `(a0 + s) / 2` of the complex method, with the root `s` that EthLib takes.
  let half := match Fp.sqrt (Fp.ofNat norm) with
    | .ok root => some ((z.c0 + root) * (Fp.ofNat 2).inverse).val
    | .error _ => none
  classify "not real, a square, the half is a square of Fp" (z.c1.val != 0 && square &&
    half.any euler)
  classify "not real, a square, the half is not a square of Fp" (z.c1.val != 0 && square &&
    half.any (!euler ·))
  match Fp2.sqrt z with
  | .ok root =>
    let back := root * root
    ensure (square && back.c0.val == z.c0.val && back.c1.val == z.c1.val)
      "a root that does not square back"
  | .error _ => ensure (!square) "a square without a root"

/-! ## Encodings -/

/-- 48 bytes near an encoding of `G1`.

They are a point of the subgroup, a point of the curve outside it, or neither.

Each comes with the three flags and the field bound changed. -/
def genG1Bytes : Gen ByteArray := do
  let k ← genNear r
  let valid : ByteArray := ⟨(G1.compress (G1.mulNat G1.generator k)).toArray⟩
  let base ← Gen.frequency [
    (5, pure valid),
    (4, (fun bs : ByteArray => bs.set! 0 (bs[0]! &&& 0x1f ||| 0x80)) <$> genBytesN 48),
    (2, pure (beBytes 48 0)),
    (1, (beBytes 48 <$> ((p + ·) <$> Gen.nat (.linear 0 3)))),
    (1, (beBytes 48 <$> ((p - ·) <$> Gen.nat (.linear 1 4)))),
    (1, (beBytes 48 <$> Gen.nat (.linear 0 8)))]
  let flags ← Gen.frequency [(6, pure none), (4, some <$> Gen.element [0x00, 0x20, 0x40, 0x60,
    0x80, 0xa0, 0xc0, 0xe0])]
  let base := match flags with
    | none => base
    | some f => base.set! 0 (base[0]! &&& 0x1f ||| f)
  Gen.frequency [(8, pure base), (1, flipBit base <$> Gen.nat (.constant 0 383))]

/-- Decompression of `G1`, the subgroup check and key validation are those of the draft. -/
def g1Decode (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex genG1Bytes
  pure do
    let expected ← oracle.ask ["g1dec", hex bytes]
    let valid ← oracle.ask ["keyvalidate", hex bytes]
    let head := bytes[0]!
    let body := beNat (bytes.set! 0 (head &&& 0x1f))
    label s!"flags {head >>> 7}{(head >>> 6) &&& 1}{(head >>> 5) &&& 1}"
    match G1.uncompress (vec 48 bytes) with
    | .ok pt =>
      classify "decoded: the point at infinity" pt.isInfinity
      classify "decoded: a point of the subgroup" (!pt.isInfinity && G1.inSubgroup pt)
      classify "decoded: a point of the curve outside the subgroup" (!G1.inSubgroup pt)
      classify "decoded: y is the larger root" (head &&& 0x20 != 0)
      classify "decoded: x is zero" (!pt.isInfinity && body == 0)
    | .error _ =>
      classify "refused: the compression flag is clear" (head &&& 0x80 == 0)
      classify "refused: the infinity flag with another bit set" (head &&& 0xc0 == 0xc0)
      classify "refused: x is p or more" (head &&& 0xc0 == 0x80 && body ≥ p)
      classify "refused: no point has this x" (head &&& 0xc0 == 0x80 && body < p)
    match G1.keyValidate (vec 48 bytes) with
    | .ok _ => label "key validation: accepted"
    | .error e => label s!"key validation: {(e.message.splitOn ":").headD ""}"
    match G1.uncompress (vec 48 bytes) with
    | .error _ =>
      expected === "error"
      valid === "0"
      ensure (G1.keyValidate (vec 48 bytes)).toOption.isNone "key validation of a refused point"
    | .ok pt =>
      render1 pt === expected
      -- The decoder accepts only what the encoder writes.
      hexVec (G1.compress pt) === hex bytes
      let inside ← if pt.isInfinity then pure "1" else oracle.ask ["g1sub", expected]
      (if G1.inSubgroup pt then "1" else "0") === inside
      (if (G1.keyValidate (vec 48 bytes)).toOption.isSome then "1" else "0") === valid

/-- 96 bytes near an encoding of `G2`.

`realY` holds points whose `y` is real: the sign of such a `y` is that of its real part. -/
def genG2Bytes (realY : List ByteArray) : Gen ByteArray := do
  let k ← genNear r
  let valid : ByteArray := ⟨(G2.compress (G2.mulNat G2.generator k)).toArray⟩
  let low ← Gen.frequency [(4, genBytesN 48 |>.map fun bs => bs.set! 0 (bs[0]! &&& 0x0f)),
    (1, beBytes 48 <$> ((p + ·) <$> Gen.nat (.linear 0 3))),
    (1, beBytes 48 <$> ((p - ·) <$> Gen.nat (.linear 1 4))),
    (1, beBytes 48 <$> Gen.nat (.linear 0 4))]
  let high ← Gen.frequency [
    (4, genBytesN 48 |>.map fun bs => bs.set! 0 (bs[0]! &&& 0x0f ||| 0x80)),
    (1, beBytes 48 <$> ((p + ·) <$> Gen.nat (.linear 0 3))),
    (1, beBytes 48 <$> ((p - ·) <$> Gen.nat (.linear 1 4))),
    (1, beBytes 48 <$> Gen.nat (.linear 0 4))]
  let real ← Gen.element (valid :: realY)
  -- The other root of a real `y` is real too: the sign flag picks it.
  let real ← Gen.element [real, real.set! 0 (real[0]! ^^^ 0x20)]
  let base ← Gen.frequency [(5, pure valid), (6, pure ((high.set! 0 (high[0]! ||| 0x80)) ++ low)),
    (2, pure real)]
  let flags ← Gen.frequency [(6, pure none), (4, some <$> Gen.element [0x00, 0x20, 0x40, 0x60,
    0x80, 0xa0, 0xc0, 0xe0])]
  let base := match flags with
    | none => base
    | some f => base.set! 0 (base[0]! &&& 0x1f ||| f)
  -- Byte 48 has no flags: its top bits are part of the second coordinate.
  let base ← Gen.frequency [(9, pure base),
    (1, (fun f : UInt8 => base.set! 48 (base[48]! ||| f)) <$> Gen.element [0x20, 0x40, 0x80])]
  Gen.frequency [(8, pure base), (1, flipBit base <$> Gen.nat (.constant 0 767))]

/-- Decompression of `G2` and its subgroup check are those of the draft. -/
def g2Decode (oracle : Oracle) (special : Specials) : Property IO := propertyM do
  let bytes ← forAllWith hex (genG2Bytes special.realY)
  pure do
    let expected ← oracle.ask ["g2dec", hex bytes]
    let head := bytes[0]!
    let c1 := beNat ((bytes.extract 0 48).set! 0 (head &&& 0x1f))
    let c0 := beNat (bytes.extract 48 96)
    label s!"flags {head >>> 7}{(head >>> 6) &&& 1}{(head >>> 5) &&& 1}"
    match G2.uncompress (vec 96 bytes) with
    | .ok pt =>
      classify "decoded: the point at infinity" pt.isInfinity
      classify "decoded: a point of the subgroup" (!pt.isInfinity && G2.inSubgroup pt)
      classify "decoded: a point of the twist outside the subgroup" (!G2.inSubgroup pt)
      classify "decoded: y is the larger root" (head &&& 0x20 != 0)
      classify "decoded: y is real, so its sign is that of c0" (!pt.isInfinity &&
        pt.toAffine.2.c1.val == 0)
      classify "decoded: x is real" (!pt.isInfinity && c1 == 0)
    | .error _ =>
      classify "refused: the compression flag is clear" (head &&& 0x80 == 0)
      classify "refused: the infinity flag with another bit set" (head &&& 0xc0 == 0xc0)
      classify "refused: the first half is p or more" (head &&& 0xc0 == 0x80 && c1 ≥ p)
      classify "refused: the second half is p or more" (head &&& 0xc0 == 0x80 && c1 < p &&
        c0 ≥ p)
      classify "refused: no point has this x" (head &&& 0xc0 == 0x80 && c1 < p && c0 < p)
    match G2.uncompress (vec 96 bytes) with
    | .error _ => expected === "error"
    | .ok pt =>
      render2 pt === expected
      hexVec (G2.compress pt) === hex bytes
      let inside ← if pt.isInfinity then pure "1" else oracle.ask ["g2sub", expected]
      (if G2.inSubgroup pt then "1" else "0") === inside

/-! ## Groups -/

/-- A point of the curve `y^2 = x^3 + 4`: of the subgroup, or of the curve only. -/
def genG1 : Gen G1 :=
  Gen.frequency [
    (4, (G1.mulNat G1.generator) <$> genNear r),
    (1, pure G1.zero),
    (3, Gen.filterMap (fun bs : ByteArray =>
      (G1.uncompress (vec 48 (bs.set! 0 (bs[0]! &&& 0x1f ||| 0x80)))).toOption) (genBytesN 48))]

/-- A point of the twist: of the subgroup, or of the twist only. -/
def genG2 : Gen G2 :=
  Gen.frequency [
    (4, (G2.mulNat G2.generator) <$> genNear r),
    (1, pure G2.zero),
    (3, Gen.filterMap (fun bs : ByteArray =>
      (G2.uncompress (vec 96 ((bs.set! 0 (bs[0]! &&& 0x1f ||| 0x80)).set! 48 (bs[48]! &&& 0x0f)))
        ).toOption) (genBytesN 96))]

/-- The sum, the double, the negative and the multiple on `G1` are py_ecc's.

This holds on the whole curve and in every mix of affine and Jacobian forms. -/
def g1Group (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAllWith (fun (a, b) => s!"{render1 a} {render1 b}") (Gen.zip genG1 genG1)
  let k ← forAll (genNear r)
  let same ← forAll (Gen.element [0, 0, 1, 2])
  pure do
    let b := if same == 1 then a else if same == 2 then G1.neg a else b
    let (ta, tb) := (render1 a, render1 b)
    classify "P is at infinity" a.isInfinity
    classify "Q is at infinity" b.isInfinity
    classify "P + Q with P = Q, a doubling" (!a.isInfinity && ta == tb)
    classify "P + Q with P = -Q, the point at infinity" (!a.isInfinity &&
      render1 (G1.neg a) == tb)
    classify "P + Q with two other points" (!a.isInfinity && !b.isInfinity && ta != tb &&
      render1 (G1.neg a) != tb)
    classify "Q has Z = 1, the mixed formulas" (!b.isInfinity && b.z.val == 1)
    classify "Q has another Z, the general formulas" (!b.isInfinity && b.z.val != 1)
    classify "P is outside the subgroup" (!G1.inSubgroup a)
    classify "the scalar is zero" (k == 0)
    classify "the scalar is r" (k == r)
    classify "the scalar is above r" (k > r)
    classify "the scalar is 1 or r - 1" (k == 1 || k + 1 == r)
    let sum ← oracle.ask ["g1add", ta, tb]
    render1 (G1.add a b) === sum
    -- The same points in Jacobian forms with `Z != 1`: three doublings minus seven times.
    let spread (pt : G1) : G1 := G1.add (G1.double (G1.double (G1.double pt))) (G1.neg
      (G1.add (G1.double (G1.double pt)) (G1.add (G1.double pt) pt)))
    render1 (spread a) === ta
    render1 (G1.add (spread a) b) === sum
    render1 (G1.add a (spread b)) === sum
    render1 (G1.add (spread a) (spread b)) === sum
    render1 (G1.double a) === (← oracle.ask ["g1add", ta, ta])
    render1 (G1.add a (G1.neg a)) === "inf"
    render1 (G1.mulNat a k) === (← oracle.ask ["g1mul", toString k, ta])
    render1 (G1.mul a (Fr.ofNat k)) === (← oracle.ask ["g1mul", toString (k % r), ta])
    ensure (G1.projectiveEq (spread a) a) "two forms of one point are not equal"
    ensure (G1.projectiveEq a b == (ta == tb)) "projective equality is not equality"
    render1 (G1.mulModulus a) === (← oracle.ask ["g1mul", toString r, ta])

/-- The same on `G2`. -/
def g2Group (oracle : Oracle) : Property IO := propertyM do
  let (a, b) ← forAllWith (fun (a, b) => s!"{render2 a} {render2 b}") (Gen.zip genG2 genG2)
  let k ← forAll (genNear r)
  let same ← forAll (Gen.element [0, 0, 1, 2])
  pure do
    let b := if same == 1 then a else if same == 2 then G2.neg a else b
    let (ta, tb) := (render2 a, render2 b)
    classify "P is at infinity" a.isInfinity
    classify "Q is at infinity" b.isInfinity
    classify "P + Q with P = Q, a doubling" (!a.isInfinity && ta == tb)
    classify "P + Q with P = -Q, the point at infinity" (!a.isInfinity &&
      render2 (G2.neg a) == tb)
    classify "P + Q with two other points" (!a.isInfinity && !b.isInfinity && ta != tb &&
      render2 (G2.neg a) != tb)
    classify "P is outside the subgroup" (!G2.inSubgroup a)
    classify "the scalar is zero" (k == 0)
    classify "the scalar is r" (k == r)
    classify "the scalar is above r" (k > r)
    classify "the scalar is 1 or r - 1" (k == 1 || k + 1 == r)
    let sum ← oracle.ask ["g2add", ta, tb]
    render2 (G2.add a b) === sum
    let spread (pt : G2) : G2 := G2.add (G2.double (G2.double (G2.double pt))) (G2.neg
      (G2.add (G2.double (G2.double pt)) (G2.add (G2.double pt) pt)))
    render2 (spread a) === ta
    render2 (G2.add (spread a) b) === sum
    render2 (G2.add a (spread b)) === sum
    render2 (G2.add (spread a) (spread b)) === sum
    render2 (G2.double a) === (← oracle.ask ["g2add", ta, ta])
    render2 (G2.add a (G2.neg a)) === "inf"
    render2 (G2.mulNat a k) === (← oracle.ask ["g2mul", toString k, ta])
    ensure (G2.projectiveEq (spread a) a) "two forms of one point are not equal"
    ensure (G2.projectiveEq a b == (ta == tb)) "projective equality is not equality"

/-- A multi-scalar multiplication is the sum of the products, one by one. -/
def msm (oracle : Oracle) : Property IO := propertyM do
  -- The largest scalar sets the number of windows, so its bit length is drawn first.
  let genTerms : Gen (List (G1 × Nat)) := do
    let bits ← Gen.frequency [(1, pure 0), (2, Gen.nat (.constant 1 8)),
      (8, Gen.nat (.constant 1 255))]
    let scalar := Gen.frequency [(1, pure 0), (1, pure (2 ^ bits - 1)),
      (4, Gen.nat (.constant 0 (2 ^ bits - 1)))]
    let terms ← Gen.frequency [
      (1, pure []),
      (6, Gen.list (.constant 1 6) (Gen.zip genG1 scalar)),
      (2, Gen.list (.constant 1 6) (Gen.zip genG1 (genNear r)))]
    -- A point twice, and a point with its opposite, land in one bucket or cancel.
    match terms with
    | (pt, k) :: rest => Gen.element [terms, (pt, k) :: (pt, k) :: rest,
        (pt, k) :: (G1.neg pt, k) :: rest, terms]
    | [] => pure terms
  let terms ← forAllWith (fun ts => toString (ts.map fun (pt, k) => (render1 pt, k))) genTerms
  let extra ← forAll (Gen.nat (.constant 0 2))
  -- The number of 8-bit windows that the largest scalar needs, as `msm` counts them.
  let bits := (terms.map fun (_, k) => if k % r == 0 then 0 else (k % r).log2 + 1).foldl max 0
  let windows := (bits + 7) / 8
  classify "no term" terms.isEmpty
  classify "every scalar is zero, so no window" (!terms.isEmpty && windows == 0)
  classify "1 window" (windows == 1)
  classify "2 to 8 windows" (2 ≤ windows && windows ≤ 8)
  classify "9 to 16 windows" (9 ≤ windows && windows ≤ 16)
  classify "17 to 31 windows" (17 ≤ windows && windows ≤ 31)
  classify "32 windows" (windows == 32)
  classify "the top window holds one bit" (bits % 8 == 1)
  classify "the top window is full" (bits > 0 && bits % 8 == 0)
  classify "a zero scalar among others" (windows > 0 && terms.any fun (_, k) => k % r == 0)
  classify "a point at infinity among the terms" (terms.any fun (pt, _) => pt.isInfinity)
  classify "a point twice" (terms.any fun (pt, _) =>
    (terms.filter fun (other, _) => render1 other == render1 pt).length > 1)
  classify "a point outside the subgroup" (terms.any fun (pt, _) => !G1.inSubgroup pt)
  classify "more points than scalars" (extra > 0)
  pure do
    let mut expected := "inf"
    for (pt, k) in terms do
      let term ← oracle.ask ["g1mul", toString (k % r), render1 pt]
      expected ← oracle.ask ["g1add", expected, term]
    let points := (terms.map (·.1)).toArray
    let scalars := (terms.map fun (_, k) => Fr.ofNat k).toArray
    render1 (G1.msm points scalars) === expected
    -- The longer array is read up to the size of the shorter.
    render1 (G1.msm (points ++ Array.replicate extra G1.generator) scalars) === expected

/-- Pairs whose pairings multiply to one, then changed. -/
def genPairs : Gen (List (Nat × Nat)) := do
  let (a, b) ← Gen.zip (genScalar r) (genScalar r)
  let balanced := [(a, b), ((r - a * b % r) % r, 1)]
  Gen.frequency [
    (3, pure balanced), (1, pure []), (1, pure [(a, b)]), (1, pure ((0, b) :: balanced)),
    (1, pure ((a, 0) :: balanced)), (1, pure [(0, 0)]),
    (1, pure [(a, b), ((a * b + 1) % r, 1)]), (1, pure [(a, b), (r - a, b)]),
    (1, pure [(a, b), (a, b), ((r - 2 * a * b % r) % r, 1)]),
    (1, pure [(1, a), (b, 1), (r - 1, (a + b) % r)])]

/-- The pairing check is arkworks': the product of the pairings is one. -/
def pairingChecks (oracle : Oracle) : Property IO := propertyM do
  let pairs ← forAll genPairs
  pure do
    let points := pairs.map fun (a, b) => (G1.mulNat G1.generator a, G2.mulNat G2.generator b)
    let expected ← oracle.ask
      ("blspairing" :: points.flatMap fun (pt, q) => [render1 pt, render2 q])
    let got := pairingCheck points.toArray
    classify "the product is one" got
    classify "the product is not one" (!got)
    classify "no pair" pairs.isEmpty
    classify "one pair" (pairs.length == 1)
    classify "three pairs" (pairs.length == 3)
    classify "a pair with the point at infinity of G1" (pairs.any fun (a, _) => a % r == 0)
    classify "a pair with the point at infinity of G2" (pairs.any fun (_, b) => b % r == 0)
    classify "every pair has a point at infinity" (!pairs.isEmpty &&
      pairs.all fun (a, b) => a % r == 0 || b % r == 0)
    (if got then "1" else "0") === expected

/-! ## Hash to curve -/

/-- A tag of a length at the edges of one byte, or short. -/
def genDst : Gen ByteArray :=
  Gen.frequency [
    (3, genBytes (.linear 1 48)),
    (3, Gen.element [0, 1, 254, 255, 256, 257, 300] >>= genBytesN),
    (2, pure Signatures.DST)]

/-- `expand_message_xmd` is that of RFC 9380 section 5.3.1, for every length and tag. -/
def expand (oracle : Oracle) : Property IO := propertyM do
  let (msg, dst) ← forAllWith (fun (m, d) => s!"{hex m} {hex d}")
    (Gen.zip (genBytes (.linear 0 200)) genDst)
  let len ← forAll (Gen.frequency [
    (4, Gen.nat (.linear 0 300)), (1, (32 * ·) <$> Gen.nat (.constant 2 255)),
    (3, Gen.element [0, 1, 31, 32, 33, 64, 8159, 8160, 8161, 65535, 65536, 65537, 2 ^ 32])])
  classify "length 0, no block kept" (len == 0)
  classify "length 1 to 32, one block" (0 < len && len ≤ 32)
  classify "length of whole blocks, two or more" (len > 32 && len % 32 == 0 && len ≤ 8160)
  classify "length that cuts the last block" (len > 32 && len % 32 != 0 && len < 8160)
  classify "length 8160, the 255 blocks" (len == 8160)
  classify "refused: 8161 to 65535, too many blocks" (8160 < len && len ≤ 65535)
  classify "refused: above 65535" (len > 65535)
  classify "tag empty" (dst.size == 0)
  classify "tag of 255 bytes, the longest kept" (dst.size == 255)
  classify "tag of 256 bytes, the shortest hashed" (dst.size == 256)
  classify "tag above 256 bytes, hashed" (dst.size > 256)
  classify "message empty" (msg.size == 0)
  pure do
    let got := match HashToCurve.expandMessageXmd msg dst len with
      | .ok out => hex out
      | .error _ => "error"
    got === (← oracle.ask ["expand", hex msg, hex dst, toString len])

/-- The branches that the simplified SWU map takes on `u`, as labels under a prefix.

They are the exceptional case, which of `x1` and `x2` is taken, and whether the sign is fixed. -/
def swuClasses (name : String) (u : Fp2) : TestT IO Unit := do
  let zu2 := HashToCurve.Z (F := Fp) * (u * u)
  let denom := zu2 * zu2 + zu2
  let x1 := if denom.isZero then HashToCurve.Bprime / (HashToCurve.Z * HashToCurve.Aprime)
    else (-HashToCurve.Bprime / HashToCurve.Aprime) * (Fp2.one + denom.inverse)
  let gx1 := x1 * x1 * x1 + HashToCurve.Aprime * x1 + HashToCurve.Bprime
  classify s!"{name}: the exceptional case, a zero denominator" denom.isZero
  let x2 := zu2 * x1
  let root := match Fp2.sqrt gx1 with
    | .ok y => some (true, y)
    | .error _ => (Fp2.sqrt (x2 * x2 * x2 + HashToCurve.Aprime * x2 +
        HashToCurve.Bprime)).toOption.map fun y => (false, y)
  match root with
  | some (first, y) =>
    classify s!"{name}: g(x1) is a square, so x1" first
    classify s!"{name}: g(x1) is not a square, so x2" (!first)
    classify s!"{name}: the sign of y is changed" (HashToCurve.sgn0Fp2 u != HashToCurve.sgn0Fp2 y)
    classify s!"{name}: the sign of y is kept" (HashToCurve.sgn0Fp2 u == HashToCurve.sgn0Fp2 y)
    classify s!"{name}: y has c0 = 0, so its sign is that of c1" (y.c0.val == 0)
    let (x, _) := if first then (x1, y) else (x2, y)
    classify s!"{name}: the isogeny has a zero denominator" (HashToCurve.isoMapG2 x y).isInfinity
  | none => label s!"{name}: no root"
  classify s!"{name}: u has c0 = 0" (u.c0.val == 0)

/-- The hash to `G2` is py_ecc's `hash_to_G2`, and its point is in the subgroup. -/
def hashToG2 (oracle : Oracle) : Property IO := propertyM do
  let (msg, dst) ← forAllWith (fun (m, d) => s!"{hex m} {hex d}")
    (Gen.zip (genBytes (.linear 0 150)) genDst)
  pure do
    match HashToCurve.hashToFieldFp2 (F := Fp) msg dst 2 with
    | .ok us =>
      swuClasses "u0" us[0]
      swuClasses "u1" us[1]
    | .error _ => label "no field elements"
    classify "tag above 255 bytes, hashed" (dst.size > 255)
    classify "tag empty" (dst.size == 0)
    classify "message empty" (msg.size == 0)
    match HashToCurve.hashToG2 (F := Fp) msg dst with
    | .ok pt =>
      render2 pt === (← oracle.ask ["h2g2any", hex msg, hex dst])
      ensure (G2.inSubgroup pt) "the hash is outside the subgroup"
    | .error _ => failWith "the hash to the curve failed"

/-- A field element at the edges, where a map to the curve has its exceptional cases. -/
def genU : Gen Nat := Gen.frequency [(2, Gen.nat (.linear 0 16)), (1, (p - ·) <$>
  Gen.nat (.linear 1 16)), (4, Gen.nat (.constant 0 (p - 1)))]

/-- The two `u` other than zero with `Z u^2 = -1` on `G1`, where the SWU map has no `x1`.

`Z = 11`, and `-1 / 11` is a square since neither `-1` nor `11` is one, as `p = 3 mod 4`. -/
def exceptionalG1 : List Nat :=
  let root := modPow p ((p - 1) * modPow p 11 (p - 2) % p) ((p + 1) / 4)
  [root, p - root]

/-- The maps of a field element to `G1` and to `G2` are py_ecc's and arkworks'. -/
def mapToCurve (oracle : Oracle) (special : Specials) : Property IO := propertyM do
  -- The inputs with a branch of their own: zero, `Z u^2 = -1`, and the kernel of the isogeny.
  let (u, v) ← forAll (Gen.frequency [
    (6, Gen.zip (Gen.frequency [(4, genU), (1, Gen.element exceptionalG1),
      (2, Gen.element special.kernelG1)]) genU),
    (2, pure (0, 0)),
    (1, (fun v => (0, v)) <$> genU)])
  pure do
    swuClasses "G2" ⟨Fp.ofNat u, Fp.ofNat v⟩
    -- The same branches of the map to `G1`, over `Fp`.
    let fu := Fp.ofNat u
    let zu2 := MapToCurve.Z (F := Fp) * (fu * fu)
    let denominator := zu2 * zu2 + zu2
    classify "G1: the exceptional case, a zero denominator" denominator.isZero
    classify "G1: u is zero" (u == 0)
    match MapToCurve.simpleSwuG1 fu with
    | .ok (x, y) =>
      let (aPrime, bPrime) : Fp × Fp := (MapToCurve.Aprime, MapToCurve.Bprime)
      let x1 := if denominator.isZero then bPrime * (MapToCurve.Z * aPrime).inverse
        else (-bPrime * aPrime.inverse) * (Fp.one + denominator.inverse)
      classify "G1: g(x1) is a square, so x1" (x.val == x1.val)
      classify "G1: g(x1) is not a square, so x2" (x.val != x1.val)
      classify "G1: y is odd, as u is" (y.val % 2 == 1)
      classify "G1: the isogeny has a zero denominator" (MapToCurve.isoMapG1 x y).isInfinity
    | .error _ => label "G1: no root"
    match MapToCurve.mapToG1 (F := Fp) (Fp.ofNat u) with
    | .ok pt => render1 pt === (← oracle.ask ["mapfp", toString u])
    | .error _ => failWith "the map to G1 failed"
    match MapToCurve.mapToG2 (F := Fp) ⟨Fp.ofNat u, Fp.ofNat v⟩ with
    | .ok pt => render2 pt === (← oracle.ask ["mapfp2", toString u, toString v])
    | .error _ => failWith "the map to G2 failed"

end CurvesProperty.Bls12
