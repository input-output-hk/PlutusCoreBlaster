import Cryptograph.Keccak.Keccak256

namespace Cryptograph.Keccak.Keccak256TestVectors

open Cryptograph.Keccak.Keccak256

/-! ## Test Vectors for Keccak-256

These test vectors are from the official Keccak test suite and Ethereum implementations.
-/

-- Empty string
/-- info: "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" -/
#guard_msgs in
#eval Keccak256.hash ""

-- "abc"
/-- info: "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" -/
#guard_msgs in
#eval Keccak256.hash "abc"

-- "The quick brown fox jumps over the lazy dog"
/-- info: "4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15" -/
#guard_msgs in
#eval Keccak256.hash "The quick brown fox jumps over the lazy dog"

-- "Hello, World!"
/-- info: "acaf3289d7b601cbd114fb36c4d29c85bbfd5e133f14cb355c3fd8d99367964f" -/
#guard_msgs in
#eval Keccak256.hash "Hello, World!"

-- "Hello World"
/-- info: "592fa743889fc7f92ac2a37bb1f5ba1daf2a5c84741ca0e0061d243a2e6707ba" -/
#guard_msgs in
#eval Keccak256.hash "Hello World"

-- "hello world"
/-- info: "47173285a8d7341e5e972fc677286384f802f8ef42a5ec5f03bbfa254cb01fad" -/
#guard_msgs in
#eval Keccak256.hash "hello world"

-- Single space
/-- info: "681afa780d17da29203322b473d3f210a7d621259a4e6ce9e403f5a266ff719a" -/
#guard_msgs in
#eval Keccak256.hash " "

-- Newline
/-- info: "0ef9d8f8804d174666011a394cab7901679a8944d24249fd148a6a36071151f8" -/
#guard_msgs in
#eval Keccak256.hash "\n"

-- Tab
/-- info: "b2e7b7a21d986ae84d62a7de4a916f006c4e42a596358b93bad65492d174c4ff" -/
#guard_msgs in
#eval Keccak256.hash "\t"

-- Special characters
/-- info: "4e48b801edfc5725e2e7b989242f0ca220b555c34862d6ec0b0e2a1a9781246c" -/
#guard_msgs in
#eval Keccak256.hash "!@#$%^&*()"

-- Quotes
/-- info: "d542c0d2590acd29c0cbeef3fb2bfd7d7241987234d676420e7f4570666f683a" -/
#guard_msgs in
#eval Keccak256.hash "\"'`"

-- Unicode: Emojis
/-- info: "b5d0c3773641e96d616afc322854b040ab615757e1bec33ad23413e243631170" -/
#guard_msgs in
#eval Keccak256.hash "😀😃😄😁😆😅😂🤣😊😇"

-- Unicode: Latin extended
/-- info: "b7a4eb7c33904dc6403eb45c715d49410588b91e3d5a909ce0bc3bae95542faa" -/
#guard_msgs in
#eval Keccak256.hash "éèêëēėę"

-- Unicode: German
/-- info: "c170d131b26edb6129d7d7470114390f58baeebffcb77c7ddbfc1e38e48db709" -/
#guard_msgs in
#eval Keccak256.hash "Müller"

-- Unicode: Spanish
/-- info: "554e41748610730b415a42375b1b310aa83431036863b326f51a63b95795c967" -/
#guard_msgs in
#eval Keccak256.hash "niño"

-- Unicode: Greek
/-- info: "a38ef57cbac45b56ce97c91fab9401faa5373fb357a95f831db32b25d28ea132" -/
#guard_msgs in
#eval Keccak256.hash "αβγ"

-- Unicode: Chinese
/-- info: "258ad79cb77e8b4964e7d7b2f962c2570978b5cf8993437233947c50889f9284" -/
#guard_msgs in
#eval Keccak256.hash "你好"

-- Unicode: Japanese
/-- info: "f852458100ef46b348a8888dec1963dc58ef1eff364daf05b1b62b2d7c6e2257" -/
#guard_msgs in
#eval Keccak256.hash "こんにちは"

-- Unicode: Korean
/-- info: "fa459986e74d9b7ea92970c98c6cf72d0057dc0e006513c2b25dd72d6fc2bfac" -/
#guard_msgs in
#eval Keccak256.hash "안녕하세요"

-- Unicode: Arabic
/-- info: "2eb10497faaf462082bab0c77471fd0fd43c3e5f9c62610adc3f364e600d34ea" -/
#guard_msgs in
#eval Keccak256.hash "مرحبا"

-- Unicode: Hebrew
/-- info: "e2a254d6b9e7e10c172781859aa10ef48f53e9c46ad804493cb9e0de7190732c" -/
#guard_msgs in
#eval Keccak256.hash "שלום"

-- Long string: 1000 'a's
partial def longStringOfAs : String :=
  let rec build (n : Nat) (acc : String) : String :=
    if n == 0 then acc else build (n - 1) (acc ++ "a")
  build 1000 ""

/-- info: "b6a4ac1f51884d71f30fa397a5e155de3099e11fc0edef5d08b646e621e19de9" -/
#guard_msgs in
#eval Keccak256.hash longStringOfAs

end Cryptograph.Keccak.Keccak256TestVectors
