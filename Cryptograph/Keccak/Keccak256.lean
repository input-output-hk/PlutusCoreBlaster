import Cryptograph.String
import Cryptograph.Integer

namespace Cryptograph.Keccak.Keccak256

/-! ## Keccak-256 Hash Implementation-/

namespace Internal

-- Type aliases
private abbrev Lane := UInt64
private abbrev State := Array (Array Lane)

-- Constants
private def stateWidth : Nat := 5
private def rounds : Nat := 24
private def rate : Nat := 136          -- 1088 bits for Keccak-256
private def capacity : Nat := 64       -- 512 bits
private def outputLength : Nat := 32   -- 256 bits

-- Rotation offsets for ρ (rho) step
private def rotationOffsets : Array (Array Nat) :=
  #[#[0, 1, 62, 28, 27],
    #[36, 44, 6, 55, 20],
    #[3, 10, 43, 25, 39],
    #[41, 45, 15, 21, 8],
    #[18, 2, 61, 56, 14]]

-- Round constants for ι (iota) step
private def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-! ### Helper Functions -/

-- Rotate left 64-bit value
private def rotl64 (x : UInt64) (n : Nat) : UInt64 :=
  let n := n % 64
  ((x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64))

-- Get state element
private def getState (state : State) (x y : Nat) : Lane :=
  state[y % stateWidth]![x % stateWidth]!

-- Set state element
private def setState (state : State) (x y : Nat) (value : Lane) : State :=
  let row := state[y % stateWidth]!
  let newRow := row.set! (x % stateWidth) value
  state.set! (y % stateWidth) newRow

-- Initialize empty state
def initState : State :=
  Array.replicate stateWidth (Array.replicate stateWidth 0)

/-! ### Keccak-f[1600] Permutation Steps -/

-- θ (theta) step: XOR each bit with parities of two columns
private def theta (state : State) : State :=
  -- Compute column parities
  let c := Array.range stateWidth |>.map fun x =>
    (List.range stateWidth).foldl (fun acc y => acc ^^^ getState state x y) 0

  -- Compute D array
  let d := Array.range stateWidth |>.map fun x =>
    c[(x + 4) % stateWidth]! ^^^ rotl64 c[(x + 1) % stateWidth]! 1

  -- Apply to state
  (List.range stateWidth).foldl (fun s y =>
    (List.range stateWidth).foldl (fun s' x =>
      setState s' x y (getState s' x y ^^^ d[x]!)
    ) s
  ) state

-- ρ (rho) step: Rotate each lane by a fixed offset
private def rho (state : State) : State :=
  (List.range stateWidth).foldl (fun s y =>
    (List.range stateWidth).foldl (fun s' x =>
      let offset := rotationOffsets[y]![x]!
      setState s' x y (rotl64 (getState s' x y) offset)
    ) s
  ) state

-- π (pi) step: Permute the positions of the lanes
private def pi (state : State) : State :=
  let newState := initState
  (List.range stateWidth).foldl (fun s y =>
    (List.range stateWidth).foldl (fun s' x =>
      let newX := y
      let newY := (2 * x + 3 * y) % stateWidth
      setState s' newX newY (getState state x y)
    ) s
  ) newState

-- χ (chi) step: Nonlinear transformation
private def chi (state : State) : State :=
  (List.range stateWidth).foldl (fun s y =>
    let row := Array.range stateWidth |>.map fun x => getState state x y
    (List.range stateWidth).foldl (fun s' x =>
      let val := row[x]! ^^^ ((~~~row[(x + 1) % stateWidth]!) &&& row[(x + 2) % stateWidth]!)
      setState s' x y val
    ) s
  ) state

-- ι (iota) step: XOR with round constant
private def iota (state : State) (roundIndex : Nat) : State :=
  let rc := roundConstants[roundIndex]!
  setState state 0 0 (getState state 0 0 ^^^ rc)

-- Complete Keccak-f[1600] round
private def keccakRound (state : State) (roundIndex : Nat) : State :=
  state |> theta |> rho |> pi |> chi |> (iota · roundIndex)

-- Apply all 24 rounds
private def keccakF (state : State) : State :=
  (List.range rounds).foldl keccakRound state

/-! ### Message Processing -/

-- Convert 8 bytes starting from offset into a Lane (UInt64, little-endian)
private def bytesToLane (bytes : ByteArray) (offset : Nat) : Lane :=
  let b0 := if offset + 0 < bytes.size then bytes[offset + 0]!.toUInt64 else 0
  let b1 := if offset + 1 < bytes.size then bytes[offset + 1]!.toUInt64 else 0
  let b2 := if offset + 2 < bytes.size then bytes[offset + 2]!.toUInt64 else 0
  let b3 := if offset + 3 < bytes.size then bytes[offset + 3]!.toUInt64 else 0
  let b4 := if offset + 4 < bytes.size then bytes[offset + 4]!.toUInt64 else 0
  let b5 := if offset + 5 < bytes.size then bytes[offset + 5]!.toUInt64 else 0
  let b6 := if offset + 6 < bytes.size then bytes[offset + 6]!.toUInt64 else 0
  let b7 := if offset + 7 < bytes.size then bytes[offset + 7]!.toUInt64 else 0
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

-- Convert a Lane (UInt64) to 8 bytes (little-endian)
private def laneToBytes (lane : Lane) : Array UInt8 :=
  #[
    (lane &&& 0xFF).toUInt8,
    ((lane >>> 8) &&& 0xFF).toUInt8,
    ((lane >>> 16) &&& 0xFF).toUInt8,
    ((lane >>> 24) &&& 0xFF).toUInt8,
    ((lane >>> 32) &&& 0xFF).toUInt8,
    ((lane >>> 40) &&& 0xFF).toUInt8,
    ((lane >>> 48) &&& 0xFF).toUInt8,
    ((lane >>> 56) &&& 0xFF).toUInt8
  ]

-- Pad the message according to the Keccak padding rule (pad10*1)
-- Note: Keccak uses 0x01 suffix, SHA3 uses 0x06
private def pad (message : ByteArray) (suffix : UInt8 := 0x01) : ByteArray :=
  let msgLen := message.size
  let blockSize := rate
  let padLen := blockSize - (msgLen % blockSize)

  let padded := message.push suffix  -- Domain separation suffix
  let padded := (List.range (padLen - 2)).foldl (fun arr _ => arr.push 0x00) padded
  padded.push 0x80  -- Final bit

-- XOR a block into the state
private def xorBlock (state : State) (block : ByteArray) (blockSize : Nat) : State :=
  let numLanes := blockSize / 8
  (List.range numLanes).foldl (fun s i =>
    let x := i % stateWidth
    let y := i / stateWidth
    let lane := bytesToLane block (i * 8)
    setState s x y (getState s x y ^^^ lane)
  ) state

-- Absorb the padded message into the state
private def absorb (state : State) (paddedMsg : ByteArray) : State :=
  let blockSize := rate
  let numBlocks := paddedMsg.size / blockSize

  (List.range numBlocks).foldl (fun s blockIdx =>
    let offset := blockIdx * blockSize
    let block := paddedMsg.extract offset (offset + blockSize)
    let s' := xorBlock s block blockSize
    keccakF s'
  ) state

-- Squeeze output from the state
private def squeeze (state : State) (outputLen : Nat) : ByteArray :=
  let result := ByteArray.emptyWithCapacity outputLen
  let numLanes := outputLen / 8

  (List.range numLanes).foldl (fun arr i =>
    let x := i % stateWidth
    let y := i / stateWidth
    let lane := getState state x y
    let bytes := laneToBytes lane
    bytes.foldl (fun a b => a.push b) arr
  ) result

/-! ### Main Hash Function -/

-- Keccak-256 hash function
-- Takes a list of bytes and returns 32-byte hash
def hashBytes (input : List UInt8) : List UInt8 :=
  let inputBytes := ByteArray.mk input.toArray
  let padded := pad inputBytes
  let state := absorb initState padded
  let outputBytes := squeeze state outputLength
  outputBytes.toList

-- Keccak-256 hash function for strings
-- Takes a string and returns hex-encoded hash
def hash (input : String) : String :=
  let inputBytes := input.toUTF8.toList
  let hashBytes := hashBytes inputBytes
  Cryptograph.String.uint8ListToHex hashBytes

/-! ### SHA3-256 Hash Function

SHA3-256 is standardized in FIPS 202 and uses the same Keccak sponge construction
but with a different padding suffix (0x06 instead of 0x01).
-/

-- SHA3-256 hash function
-- Takes a list of bytes and returns 32-byte hash
def sha3_256_hashBytes (input : List UInt8) : List UInt8 :=
  let inputBytes := ByteArray.mk input.toArray
  let padded := pad inputBytes 0x06  -- SHA3 domain separation
  let state := absorb initState padded
  let outputBytes := squeeze state outputLength
  outputBytes.toList

-- SHA3-256 hash function for strings
-- Takes a string and returns hex-encoded hash
def sha3_256_hash (input : String) : String :=
  let inputBytes := input.toUTF8.toList
  let hashBytes := sha3_256_hashBytes inputBytes
  Cryptograph.String.uint8ListToHex hashBytes

end Internal

-- Export main functions
export Internal (hashBytes hash sha3_256_hashBytes sha3_256_hash)

end Cryptograph.Keccak.Keccak256
