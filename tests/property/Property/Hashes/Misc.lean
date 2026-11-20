import Property.Hashes.Cipher
import EthLib.Cryptography.Rfc6979
import EthLib.Cryptography.Keystore
import EthLib.Cryptography.Ethash
import EthLib.Cryptography.Merkle

/-!
# RFC 6979 nonces, ERC-2335 keystores, Ethash and the Merkle tree
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace HashesProperty

/-! ## RFC 6979 -/

/-- The orders of secp256k1 and of P-256. -/
def orders : List Nat :=
  [0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
    0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551]

/-- A group order of 256 bits: one of the two curves, or any number with its top bit set.

`nonceSeed` takes the order as a number, and its text asks only that it has 256 bits. -/
def genOrder : Gen Nat :=
  Gen.frequency [(3, Gen.element orders), (1, Gen.element [2 ^ 255, 2 ^ 255 + 1, 2 ^ 256 - 1]),
    (2, (2 ^ 255 + ·) <$> genNatBits 255)]

/-- A 256-bit number near an order: just below it, on it, just above, or any. -/
def genNearOrder (q : Nat) : Gen Nat :=
  Gen.frequency [(3, genNatBits 256), (1, pure 0),
    (3, (fun d => (q + 2 - d) % 2 ^ 256) <$> Gen.nat (.constant 0 4)),
    (1, pure (2 ^ 256 - 1))]

/-- The seeded generator is that of RFC 6979 §3.2, steps b to g, for any order of 256 bits.

A hash at or above the order is reduced by `bits2octets`, so those are drawn often. -/
def rfc6979Seed (oracle : Oracle) : Property IO := propertyM do
  let q ← forAll genOrder
  let x ← forAll (genNearOrder q)
  let hash ← forAll (Gen.choice [genBytesOf 32, beBytes 32 <$> genNearOrder q])
  let h := Base.bytesToNat hash.toList
  classify "order: of secp256k1" (q == orders.headD 0)
  classify "order: of P-256" (q == orders.getD 1 0)
  classify "order: another number of 256 bits" (!orders.contains q)
  classify "hash: below the order" (h < q)
  classify "hash: the order exactly" (h == q)
  classify "hash: above the order, reduced" (h > q)
  classify "key: zero" (x == 0)
  classify "key: below the order" (0 < x && x < q)
  classify "key: the order or more" (x ≥ q)
  pure do
    let state := Rfc6979.nonceSeed q x (vec 32 hash)
    s!"{hex state.key} {hex state.value}"
      === (← oracle.ask ["rfc_seed", toString q, toString x, hex hash])

/-! ## ERC-2335 keystores -/

/-- A character of a password.

It is ASCII, a control code that is stripped, or a character that NFKD decomposes.

It can also be a character outside the basic plane. -/
def genPasswordChar : Gen Char :=
  Gen.frequency [
    (4, Gen.char (.constant ' ' '~')),
    (2, Gen.char (.constant (Char.ofNat 0) (Char.ofNat 0x1f))),
    (2, Gen.char (.constant (Char.ofNat 0x7f) (Char.ofNat 0xa0))),
    (2, Gen.element ['é', 'Å', 'ﬁ', 'ｶ', '①', 'ǆ', '𝔱', '🔑']),
    -- Each side of the two ranges of control codes that the ERC strips.
    (2, Gen.element ([0x1f, 0x20, 0x7e, 0x7f, 0x9f, 0xa0].map Char.ofNat)),
    (1, Gen.char (.constant (Char.ofNat 0xa0) (Char.ofNat 0x24f)))]

/-- A password of such characters. -/
def genPassword : Gen String := Gen.string (.linear 0 12) genPasswordChar

/-- The code points of a string, to show a password whose characters do not print. -/
def codePoints (s : String) : String :=
  " ".intercalate (s.toList.map fun c => String.ofList (Nat.toDigits 16 c.toNat))

/-- What is changed in a keystore before it is opened.

Each change but `upper` and `extra` makes a keystore that ERC-2335 refuses. -/
def mutations : List String :=
  ["checksum", "cipher", "version", "version5", "versiontext", "upper", "extra", "nopath",
    "nouuid", "nopubkey", "nodescription", "numpath", "numpubkey", "numdescription", "prf",
    "cipherfn", "checksumfn", "kdffn", "iv15", "iv17", "noiv", "oddhex", "nothex", "prefix",
    "checksum31", "checksum33", "nomessage", "noparams", "listparams", "nocrypto", "nokdf",
    "nochecksum", "nocipher", "nosalt", "nodklen", "nocost", "dklentext"]

/-- The changes to the cost of a key derivation: none, one, not a power of two, no block. -/
def costMutations : List String := ["cost0", "cost1", "cost3", "r0", "p0"]

/-- The parameters of a small key derivation: the function, its cost, `r`, `p`. -/
def genKdf : Gen (String × Nat × Nat × Nat) :=
  Gen.choice [
    (fun c => ("pbkdf2", c, 0, 0)) <$> Gen.nat (.constant 1 3),
    Gen.zipWith (fun n rp => ("scrypt", n, rp.1, rp.2)) (Gen.element [2, 4, 8])
      (Gen.zip (Gen.nat (.constant 1 2)) (Gen.nat (.constant 1 2)))]

/-- How the caller's limit stands to the cost of the derivation, for memory and for work.

`0` is no limit to speak of, `1` the cost exactly, `2` one unit under it, `3` one unit over. -/
def genLimits : Gen (Nat × Nat) :=
  Gen.frequency [(5, pure (0, 0)), (2, pure (1, 1)),
    (4, Gen.zip (Gen.nat (.constant 0 3)) (Gen.nat (.constant 0 3)))]

/-- A limit from the cost and its kind. -/
def limitOf (cost kind : Nat) : Nat :=
  match kind with
  | 1 => cost
  | 2 => cost - 1
  | 3 => cost + 1
  | _ => 2 ^ 30

/-- Decryption of a keystore is that of ERC-2335.

The reference writes the keystore of a secret, and changes one thing in it or not.

EthLib opens it exactly when the reference does, with the same secret.

The password is normalized and stripped of control codes.

These are refused:

- A wrong password.
- A changed checksum or ciphertext.
- A missing required field, or a field of another type.
- An unsupported function, and a cost that the function refuses.
- A derived key of fewer than 32 bytes.
- A derivation that costs more than the caller allows, in memory or in work.

The work is counted by the reference while it derives the key, and the memory is EthLib's model. -/
def keystore (oracle : Oracle) : Property IO := propertyM do
  let (kdf, cost, r, p) ← forAll genKdf
  let dklen ← forAll (Gen.frequency [(6, Gen.element [32, 33, 48, 64]),
    (1, Gen.element [31, 16, 1, 0])])
  let (salt, iv) ← forAll (Gen.zip (genBytes (.linear 0 40)) genCounter)
  let password ← forAllWith codePoints genPassword
  let tried ← forAllWith codePoints (Gen.frequency [(6, pure password), (1, genPassword)])
  let secret ← forAll (do genBytesN (← Gen.frequency [(3, pure 32), (1, pure 0),
    (1, Gen.element [16, 17, 48]), (3, Gen.nat (.linear 0 40))]))
  -- A change to a field that the function does not have would change nothing.
  let mutation ← forAll (Gen.frequency [(8, pure "none"),
    (12, Gen.element (mutations.filter fun m => m != "prf" || kdf == "pbkdf2")),
    (5, Gen.element (if kdf == "pbkdf2" then ["cost0", "prf"] else costMutations)),
    (1, Gen.element ["version", "version5", "versiontext"])])
  let (memoryKind, workKind) ← forAll genLimits
  label s!"kdf: {kdf}"
  label s!"change: {mutation}"
  classify "password: the one that sealed" (tried == password)
  classify "password: holds a control code" (password.toList.any Keystore.isControl)
  classify "password: holds a character that NFKD changes"
    (Base.Unicode.nfkd password != password)
  classify "password: holds the first or the last of a range of control codes"
    (password.toList.any fun c => [0x1f, 0x7f, 0x9f].contains c.toNat)
  classify "password: holds a character next to a range of control codes"
    (password.toList.any fun c => [0x20, 0x7e, 0xa0].contains c.toNat)
  classify "secret: empty" secret.isEmpty
  classify "secret: 32 bytes, as a BLS key" (secret.size == 32)
  classify "secret: more than one block of the cipher" (secret.size > 16)
  classify "derived key: longer than 32 bytes" (dklen > 32)
  classify "derived key: 16 to 31 bytes, sealed as the slices of the ERC read it"
    (16 ≤ dklen && dklen < 32)
  classify "derived key: shorter than 16 bytes" (dklen < 16)
  pure do
    let answer ← oracle.ask ["ks", mutation, kdf, toString cost, toString r,
      toString p, toString dklen, hex salt, hex iv, hex password.toUTF8, hex tried.toUTF8,
      hex secret]
    let [store, unlimited, memory, work] := answer.splitOn " "
      | failWith s!"the reference answered {answer}"
    let (memory, work) := (memory.toNat!, work.toNat!)
    let some text := (unhex? store).bind String.fromUTF8? | failWith "the keystore is not text"
    let .ok json := Lean.Json.parse text | failWith "the keystore is not JSON"
    -- The reference gives a cost only for a derivation that it runs.
    let known := memory > 0
    let limits : Keystore.KdfLimits := if known then
      ⟨limitOf memory memoryKind, limitOf work workKind⟩ else ⟨2 ^ 30, 2 ^ 30⟩
    let within := !known || (memoryKind != 2 && workKind != 2)
    let expected := if within then unlimited else "error"
    classify "cost: the reference ran the derivation and counted its work" known
    classify "limit: the memory exactly" (known && memoryKind == 1)
    classify "limit: one byte under the memory" (known && memoryKind == 2)
    classify "limit: the work exactly" (known && workKind == 1)
    classify "limit: one unit under the work" (known && workKind == 2)
    classify "limit: on both costs exactly, opened"
      (known && memoryKind == 1 && workKind == 1 && unlimited != "error")
    let got := Keystore.decrypt limits json tried
    annotate (reprStr got)
    annotate s!"memory {memory}, work {work}, limits {limits.memory} and {limits.work}"
    labelOutcome got
    (match got with | .ok bytes => hex bytes | .error _ => "error") === expected
    if mutation == "none" && tried == password && within && dklen ≥ 32 then
      expected === hex secret
    -- The models of EthLib give the cost that the reference counted.
    if known then
      if let .ok parsed := Keystore.readStore json then
        parsed.kdf.memory === memory
        parsed.kdf.work (Keystore.passwordBytes tried).size === work

/-- The scrypt test vector of ERC-2335, "Test Cases". -/
def scryptVector : String :=
    "{\"crypto\":{\"kdf\":{\"function\":\"scrypt\",\"params\":{\"dklen\":32,\"n\":262144," ++
    "\"p\":1,\"r\":8,\"salt\":\"d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db" ++
    "1cb8fa3\"},\"message\":\"\"},\"checksum\":{\"function\":\"sha256\",\"params\":{},\"m" ++
    "essage\":\"d2217fe5f3e9a1e34581ef8a78f7c9928e436d36dacc5e846690a5581e8ea484\"},\"cip" ++
    "her\":{\"function\":\"aes-128-ctr\",\"params\":{\"iv\":\"264daa3f303d7259501c93d997d" ++
    "84fe6\"},\"message\":\"06ae90d55fe0a6e9c5c3bc5b170827b2e5cce3929ed3f116c2811e6366dfe" ++
    "20f\"}},\"description\":\"This is a test keystore that uses scrypt to secure the sec" ++
    "ret.\",\"pubkey\":\"9612d7a727c9d0a22e185a1c768478dfe919cada9266988cb32359c11f2b7b27" ++
    "f4ae4040902382ae2910c15e2b420d07\",\"path\":\"m/12381/60/3141592653/589793238\",\"uu" ++
    "id\":\"1d85ae20-35c5-4611-98e8-aa14a633906f\",\"version\":4}"

/-- The PBKDF2 test vector of ERC-2335, "Test Cases". -/
def pbkdf2Vector : String :=
    "{\"crypto\":{\"kdf\":{\"function\":\"pbkdf2\",\"params\":{\"dklen\":32,\"c\":262144," ++
    "\"prf\":\"hmac-sha256\",\"salt\":\"d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69" ++
    "aec8c0db1cb8fa3\"},\"message\":\"\"},\"checksum\":{\"function\":\"sha256\",\"params\"" ++
    ":{},\"message\":\"8a9f5d9912ed7e75ea794bc5a89bca5f193721d30868ade6f73043c6ea6febf1\"" ++
    "},\"cipher\":{\"function\":\"aes-128-ctr\",\"params\":{\"iv\":\"264daa3f303d7259501c" ++
    "93d997d84fe6\"},\"message\":\"cee03fde2af33149775b7223e7845e4fb2c8ae1792e5f99fe9ecf4" ++
    "74cc8c16ad\"}},\"description\":\"This is a test keystore that uses PBKDF2 to secure " ++
    "the secret.\",\"pubkey\":\"9612d7a727c9d0a22e185a1c768478dfe919cada9266988cb32359c11" ++
    "f2b7b27f4ae4040902382ae2910c15e2b420d07\",\"path\":\"m/12381/60/0/0\",\"uuid\":\"646" ++
    "25def-3331-4eea-ab6f-782f3ed16a83\",\"version\":4}"

/-- Both test vectors of ERC-2335 open to the secret of the ERC, under its password.

Each derivation costs 262144 units, so this runs once and only when asked. -/
def keystoreVectors : Property IO := pureIO do
  let password := "𝔱𝔢𝔰𝔱𝔭𝔞𝔰𝔰𝔴𝔬𝔯𝔡🔑"
  hex (Keystore.passwordBytes password) === "7465737470617373776f7264f09f9491"
  for vector in [pbkdf2Vector, scryptVector] do
    let .ok json := Lean.Json.parse vector | failWith "the vector is not JSON"
    let got := Keystore.decrypt ⟨2 ^ 32, 2 ^ 32⟩ json password
    (match got with | .ok bytes => hex bytes | .error e => reprStr e)
      === "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"

/-! ## Ethash -/

/-- The bytes of some items, in order. -/
def itemBytes (items : Array Ethash.Item) : ByteArray :=
  items.foldl (fun out item => out ++ Ethash.bytesOfWords item) .empty

/-- A block number: in the first epochs, at the edges of an epoch, or up to epoch 2047. -/
def genBlock : Gen Nat :=
  Gen.frequency [
    (2, Gen.nat (.linear 0 (30000 * 2048))),
    (1, Gen.element [0, 1, 29999, 30000, 30001, 59999, 60000]),
    (1, Gen.nat (.constant 0 29999)),
    (4, Gen.zipWith (fun e d => e * 30000 + 1 - d) (Gen.nat (.linear 1 2047))
      (Gen.nat (.constant 0 2)))]

/-- The cache size and the dataset size of an epoch are those of the specification. -/
def ethashSizes (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll genBlock
  classify "epoch: 0" (block < 30000)
  classify "block: the first of its epoch" (block % 30000 == 0)
  classify "block: the last of its epoch" (block % 30000 == 29999)
  classify "epoch: past 512, beyond the chain's last" (block / 30000 > 512)
  pure do
    -- The search starts one unit below the linear size, and may stay there.
    classify "cache: the first candidate is prime"
      (Ethash.cacheSize block == 2 ^ 24 + 2 ^ 17 * (block / 30000) - 64)
    classify "dataset: the first candidate is prime"
      (Ethash.datasetSize block == 2 ^ 30 + 2 ^ 23 * (block / 30000) - 128)
    s!"{Ethash.cacheSize block} {Ethash.datasetSize block}"
      === (← oracle.ask ["ethash_sizes", toString block])

/-- The sizes of every epoch from 0 to 2047 are those of the specification.

A random block number reaches an epoch at most once, and most epochs never.

The chain ended its proof of work in epoch 517, and the sizes are a table for any epoch. -/
def ethashEpochs (oracle : Oracle) : Property IO := propertyM do
  pure do
    for chunk in List.range 16 do
      let answer ← oracle.ask ["ethash_epochs", toString (128 * chunk), "128"]
      for (text, i) in (answer.splitOn " ").zipIdx do
        let e := 128 * chunk + i
        let got := s!"{Ethash.cacheSize (30000 * e)}:{Ethash.datasetSize (30000 * e + 29999)}"
        if got != text then annotate s!"epoch {e}"
        got === text

/-- Primality by trial division is primality, at the squares of primes too.

The size search is the loop of the specification.

The loop goes from `x`, down by two units while the quotient is composite. -/
def ethashPrimes : Property IO := pureIO do
  let n ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 2000)),
    (2, (fun p => p * p) <$> Gen.nat (.linear 0 300)), (1, Gen.nat (.exponential 0 (2 ^ 24)))])
  let prime := n ≥ 2 && (List.range n).all fun d => d < 2 || d * d > n || n % d != 0
  classify "number: 0 or 1" (n < 2)
  classify "number: prime" prime
  classify "number: the square of a prime"
    ((List.range 301).any fun p => p * p == n && p ≥ 2 &&
      (List.range p).all fun d => d < 2 || p % d != 0)
  classify "number: composite" (n ≥ 2 && !prime)
  Ethash.isPrime n === prime
  let unit ← forAll (Gen.element [1, 64, 128])
  let x ← forAll (Gen.nat (.linear (20 * unit) (4000 * unit)))
  let search := (List.range 2000).foldl (fun x _ =>
    if Ethash.isPrime (x / unit) then x else x - 2 * unit) x
  classify "search: the first candidate is prime" (search == x)
  classify "search: several steps down" (search + 2 * unit < x)
  label s!"search: unit {unit}"
  Ethash.primeSize x unit === search

/-- The seed of an epoch is the specification's. -/
def ethashSeed (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll (Gen.zipWith (fun e d => e * 30000 + 1 - d)
    (Gen.frequency [(1, Gen.element [1, 2]), (3, Gen.nat (.linear 1 60))])
    (Gen.nat (.constant 0 2)))
  classify "epoch: 0, the seed is zeros" (block < 30000)
  classify "epoch: 1" (block / 30000 == 1)
  classify "epoch: 2 or more" (block / 30000 > 1)
  classify "block: the first or the last of its epoch"
    (block % 30000 == 0 || block % 30000 == 29999)
  pure do hex (Ethash.seed block) === (← oracle.ask ["ethash_seed", toString block])

/-- The cache of `n` items from a seed: the chain of digests, then three rounds. -/
def tinyCache (n : Nat) (seed : ByteArray) : Array Ethash.Item :=
  Nat.repeat Ethash.cacheRound Ethash.CACHE_ROUNDS (Ethash.initialCache n seed)

/-- A cache of a few items, a dataset item and the proof of work from it are the specification's. -/
def ethashPow (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (Gen.nat (.linear 1 40))
  let seed ← forAll (genBytesOf 32)
  let index ← forAll (genNatBits 32)
  let size ← forAll (Gen.zipWith (fun pairs rest => 128 * pairs + rest)
    (Gen.frequency [(1, Gen.element [1, 2]), (6, Gen.nat (.linear 1 200))])
    (Gen.element [0, 0, 64, 127]))
  let (header, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 8))
  classify "cache: one item" (n == 1)
  classify "cache: two items" (n == 2)
  classify "cache: more than 16 items" (n > 16)
  classify "dataset: one pair of items" (size / 128 == 1)
  classify "dataset: its size is not whole pairs" (size % 128 != 0)
  classify "index: beyond the cache" (index ≥ n)
  classify "index: 2^31 or more" (index ≥ 2 ^ 31)
  pure do
    let cache := tinyCache n seed
    hex (itemBytes cache) === (← oracle.ask ["ethash_cache", toString n, hex seed])
    hex (Ethash.bytesOfWords (Ethash.datasetItem cache index))
      === (← oracle.ask ["ethash_item", toString n, hex seed, toString index])
    let pow := Ethash.hashimotoLight size cache header nonce
    s!"{hex pow.mixDigest} {hex pow.result}" === (← oracle.ask ["ethash_pow", toString n,
      hex seed, toString size, hex header, hex nonce])

/-- The cache of epoch 0, all 262139 items of it, is the specification's.

So are a dataset item and the proof of work over the dataset size of that epoch.

The cache takes a million Keccak-512 digests on each side, so this runs once and only when asked. -/
def ethashEpoch (oracle : Oracle) : Property IO := propertyM do
  let index ← forAll (genNatBits 32)
  let (header, nonce) ← forAll (Gen.zip (genBytesOf 32) (genBytesOf 8))
  pure do
    let cache := Ethash.cache 0
    let n := Ethash.cacheSize 0 / 64
    cache.size === n
    let seed := Ethash.seed 0
    hexv (Hash.Keccak.keccak256 (itemBytes cache))
      === (← oracle.ask ["ethash_cache_hash", toString n, hex seed])
    hex (Ethash.bytesOfWords (Ethash.datasetItem cache index))
      === (← oracle.ask ["ethash_item", toString n, hex seed, toString index])
    let pow := Ethash.hashimotoLight (Ethash.datasetSize 0) cache header nonce
    s!"{hex pow.mixDigest} {hex pow.result}" === (← oracle.ask ["ethash_pow", toString n,
      hex seed, toString (Ethash.datasetSize 0), hex header, hex nonce])

/-! ## The Merkle tree

The node hash is a term that names its position and its children.

So two different trees never share a root.

The model is a list of levels built from the leaves up. -/

open Merkle in
/-- The symbolic node hash: the position and both children, written out. -/
def symbolic (p : Position) (left right : String) : Id String :=
  pure s!"({p.level}.{p.index} {left} {right})"

/-- The levels of the tree over the leaves, from the leaves up to the root. -/
def levels (leaves : List String) : (h : Nat) → List (List String)
  | 0 => [leaves]
  | h + 1 =>
    let below := levels leaves h
    let last := below.getLastD []
    below ++ [(List.range (last.length / 2)).map fun j =>
      s!"({h + 1}.{j} {last.getD (2 * j) "?"} {last.getD (2 * j + 1) "?"})"]

/-- The node of the model at a position. -/
def modelNode (tree : List (List String)) (p : Merkle.Position) : String :=
  (tree.getD p.level []).getD p.index "?"

/-- A height and the `2^h` leaves of a tree. -/
def genTree : Gen (Nat × List String) := do
  let h ← Gen.frequency [(1, pure 0), (1, pure 1), (6, Gen.nat (.constant 2 6))]
  let leaves ← Gen.list (.singleton (2 ^ h)) (Gen.string (.constant 1 2) Gen.lower)
  pure (h, leaves)

/-- The leaves of a list as the function a tree reads. -/
def leafAt (leaves : List String) (j : Nat) : Id String := pure (leaves.getD j "?")

/-- Every node, every path and every climb of a tree are those of the model. -/
def merkleTree : Property IO := pureIO do
  let (h, leaves) ← forAll genTree
  let j ← forAll (Gen.nat (.constant 0 (2 ^ h - 1)))
  let level ← forAll (Gen.nat (.constant 0 h))
  label s!"height: {h}"
  classify "leaf: the first" (j == 0)
  classify "leaf: the last" (j + 1 == 2 ^ h)
  classify "node: a leaf" (level == 0)
  classify "node: the root" (level == h)
  let tree := levels leaves h
  let root := modelNode tree ⟨h, 0⟩
  Id.run (Merkle.root symbolic (leafAt leaves) h) === root
  let p : Merkle.Position := ⟨level, j / 2 ^ level⟩
  Id.run (Merkle.node symbolic (leafAt leaves) p) === modelNode tree p
  let path := (Id.run (Merkle.path symbolic (leafAt leaves) h j)).toList
  path === (List.range h).map fun k => modelNode tree ⟨k, (j / 2 ^ k) ^^^ 1⟩
  Id.run (Merkle.climb symbolic ⟨0, j⟩ (leaves.getD j "?") path) === root
  -- A path with one sibling changed climbs to another root.
  if h > 0 then
    let k ← forAll (Gen.nat (.constant 0 (h - 1)))
    Id.run (Merkle.climb symbolic ⟨0, j⟩ (leaves.getD j "?") (path.set k "!")) /== root

/-- Every position of the tree of height `h`, the root included. -/
def positions (h : Nat) : List Merkle.Position :=
  (List.range (h + 1)).flatMap fun level =>
    (List.range (2 ^ (h - level))).map fun index => ⟨level, index⟩

/-- The positions that have no other of the list above them. -/
def antichain (ps : List Merkle.Position) : List Merkle.Position :=
  ps.filter fun p => !ps.any fun a => a != p && a.covers p

/-- The helpers by their definition.

They are the siblings of the path nodes that are not path nodes.

They run from the leaves up, and from right to left within a level. -/
def modelHelpers (h : Nat) (opened : List Merkle.Position) : List Merkle.Position :=
  let paths := (opened.flatMap (Merkle.pathTo h)).eraseDups
  let siblings := (paths.map (·.sibling)).eraseDups.filter (!paths.contains ·)
  siblings.mergeSort fun a b => a.level < b.level || (a.level == b.level && b.index ≤ a.index)

/-- Positions to open in the tree of height `h`, before the ones under another are dropped.

Each is a leaf, or the ancestor of a leaf at some level, so the root is opened only now and then.

A draw of any subset of the positions holds the root half the time, and the root covers all. -/
def genOpened (h : Nat) : Gen (List Merkle.Position) :=
  let one : Gen Merkle.Position :=
    Gen.zipWith (fun j level => ⟨level, j / 2 ^ level⟩) (Gen.nat (.constant 0 (2 ^ h - 1)))
      (Gen.frequency [(4, pure 0), (2, Gen.nat (.constant 0 (h - 1))),
        (1, Gen.nat (.constant 0 h))])
  Gen.frequency [
    (8, Gen.list (.constant 1 8) one),
    (1, pure [⟨h, 0⟩]),
    (1, pure ((List.range (2 ^ h)).map fun j => ⟨0, j⟩)),
    (1, Gen.subsequence (positions h) >>= Gen.shuffle)]

/-- A multiproof of nodes on any levels rebuilds the root of the model.

Its helpers are those of their definition.

With one opened value changed it rebuilds another root or none. -/
def merkleMultiproof : Property IO := pureIO do
  let (h, leaves) ← forAll genTree
  let first ← forAllWith reprStr (Gen.element (positions h))
  let more ← forAllWith reprStr (genOpened h)
  -- The first position is kept only where the others leave the tree unopened.
  let opened := antichain (if more.isEmpty then [first] else more).eraseDups
  label s!"height: {h}"
  classify "opened: one node" (opened.length == 1)
  classify "opened: the root alone" (opened == [⟨h, 0⟩])
  classify "opened: leaves only, several" (opened.length > 1 && opened.all (·.level == 0))
  classify "opened: every leaf" (opened.length == 2 ^ h && opened.all (·.level == 0))
  classify "opened: nodes of several levels" ((opened.map (·.level)).eraseDups.length > 1)
  classify "opened: two siblings, which need no helper between them"
    (opened.any fun p => opened.contains p.sibling)
  classify "opened: not in order of position"
    (opened != opened.mergeSort fun a b => a.level < b.level ||
      (a.level == b.level && a.index ≤ b.index))
  classify "helpers: none" (Merkle.helpers h opened).isEmpty
  classify "helpers: on several levels"
    (((Merkle.helpers h opened).map (·.level)).eraseDups.length > 1)
  classify "helpers: two or more on one level"
    (let levels := (Merkle.helpers h opened).map (·.level)
     levels.eraseDups.length < levels.length)
  let tree := levels leaves h
  let root := modelNode tree ⟨h, 0⟩
  let helpers := Merkle.helpers h opened
  helpers === modelHelpers h opened
  let values := opened.map (modelNode tree)
  let helperValues := helpers.map (modelNode tree)
  Id.run (Merkle.verify symbolic h opened values helperValues) === some root
  let k ← forAll (Gen.nat (.constant 0 (opened.length - 1)))
  Id.run (Merkle.verify symbolic h opened (values.set k "!") helperValues) /== some root
  -- One helper too few does not determine the root.
  if !helpers.isEmpty then
    Id.run (Merkle.verify symbolic h opened values helperValues.dropLast) === none
  -- One helper value changed rebuilds another root.
  if !helpers.isEmpty then
    let i ← forAll (Gen.nat (.constant 0 (helpers.length - 1)))
    Id.run (Merkle.verify symbolic h opened values (helperValues.set i "!")) /== some root

end HashesProperty
