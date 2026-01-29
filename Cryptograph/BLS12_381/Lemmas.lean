import Cryptograph.String
import Cryptograph.BLS12_381.Basic

namespace Cryptograph.BLS12_381

open Cryptograph.String
open Cryptograph.BLS12_381.Internal

theorem g1_times_groupOrder : groupOrder * g1 = .infinity := by native_decide
theorem g2_times_groupOrder : groupOrder * g2 = .infinity := by native_decide

namespace Tests

-- example : 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218 * g1 =
--   .affine 0x019906b4953328ec688ffc9e41ea7d79d295c7de6249eb0397680306c5fe3aa3bbb45324bdbc379e8e4116166f2a0d40
--           0x165f11693959e7193af31b99b724f95d7b49baa2394b758c2455ef725f32abd56361e1e151f2bbd7a7efc6f3bb5652d4 := by native_decide

-- example : 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218 * g2 =
--   .affine { u1 := 0x02433912fa403e0d19d39c7687eb1041f474a82fdd646b1a35afb4d088f11469467468f1ba16c3e5838503919bdbfa24
--           , u0 := 0x14906db96db027e17449a1323198cfccde4d15456ce09f3fef4c7baed5495463b7cc750300e0e2918d5680d97a567122 }
--           { u1 := 0x0e82e52250625e4c0864645fba3b36e24c36dbc3d4bae0ca40b0c28b0e3780bf6b8d022c032727e8195e2a2b547be84b
--           , u0 := 0x0f240b0ffee3ac62cd5576f012a92cd78c9ded14c11c7637caff4daf885c9a258783a7aef4dc1815737a5b606e03868e } := by native_decide

-- example : (31 * g1) + (-21 * g1) = 10 * g1 := by native_decide
-- example : (31 * g1) + (-30 * g1) =      g1 := by native_decide
-- example : (31 * g2) + (-21 * g2) = 10 * g2 := by native_decide
-- example : (31 * g2) + (-30 * g2) =      g2 := by native_decide

-- def p1 : Point Fq1 :=
--   .affine 0x14ade5f375a7e7194bf5244ace032817f63ff854f22654e3c0855511156fe98ba5c092ad9d68011f783e0f418619b2f2
--           0x0b54adeba0fdaeeaec7a7146c738c7ebf3f44158475541427ce976fe020e52dedd97feba12c7272b8f3dc49a7d122f8d

-- example : isOnCurve    p1 = true := by native_decide
-- example : isInSubGroup p1 = true := by native_decide

-- def q1 : Point Fq2 :=
--   .affine { u1 := 0x14ebc73c50a68b2333c169565ab75e35c03caaae6573884db2557a6731eca4c643bf7156cb6a2fee60b079577d4732e6
--           , u0 := 0x064974dc7ff588a0b38e37da6b767b91d068924526dd8698f131b6f19b309065aab861b33411675781d9d42b63935c85 }
--           { u1 := 0x16048641e0249a5ff6cb1b4a8c9194589148c1903b800752d8a6c09867508952d14fecb015cc4f337372b29bc32b08b1
--           , u0 := 0x172f08bfdf8fca06c461c9978e8d8f7de5126a9ee74d086a82d90545d9180e3f9199a7fd2fbd022a9bcfa833ec321e0a }

-- example : isOnCurve    q1 = true := by native_decide
-- example : isInSubGroup q1 = true := by native_decide

-- def p2 : Point Fq1 :=
--   .affine 0x19097e1378ae74067593c7e6b71fc8ec41d11e8e1b67b9ca47475e2eb02d5959cfb4bb09a3cb4c7fc14506629b4176d1
--           0x0e41648923fc4a39b9e0e0f3d4b0fdcae45caad07622e2d40e67d2eea13bff92f071c0cf4b6687417efdadfae4fec00a

-- example : isOnCurve    p2 = true := by native_decide
-- example : isInSubGroup p2 = true := by native_decide

-- def q2 : Point Fq2 :=
--   .affine { u1 := 0x0da18340291cbdd3cfaf596d62fe88f4cf211e8a2439f736786c12fba4e66cccb9279ef1a814d81785bec778c60f9284
--           , u0 := 0x0a1d6930cfb119d6b2c52f8260217bf7859437e6aa8b8ca891ce74886f7c667274507b6f107a0c4c7618fe2f3571fcb2 }
--           { u1 := 0x009745aac53daa7296110ad436829ec3cfd8fbc83012878608479a11caf2ada57c95dd64fd5fd3d4cf3cdf536defd288
--           , u0 := 0x1831856291ad777b5e8f2eff3c2a4efe23a56f44ad97cda5c77f5a9c51bef1e13691011ab1979568363f5b1fecdd32d6 }

-- example : isOnCurve    q2 = true := by native_decide
-- example : isInSubGroup q2 = true := by native_decide

-- example : (calculatePairing p1 q1 |> Option.isSome) = true := by native_decide
-- example : calculatePairing p1 q1 = calculatePairing p2 q2 := by native_decide

-- example : calculatePairing (123 * g1) (3224 * g2) = calculatePairing (3224 * g1) (123 * g2) := by native_decide

-- def Option.mul {α} [Mul α] (a b : Option α) : Option α := (· * ·) <$> a <*> b

-- instance {α} [Mul α] : Mul (Option α) where
--   mul := Option.mul

-- example : (calculatePairing (((12 + 34) * 56) * g1) (78 * g2) |> Option.isSome) = true := by native_decide
-- example : calculatePairing (((12 + 34) * 56) * g1) (78 * g2)
--           = calculatePairing (78 * g1) ((12 * 56) * g2) * calculatePairing (78 * g1) ((34 * 56) * g2) := by native_decide

-- example : (calculatePairing ((12 + 34 + 56) * g1) (78 * g2) |> Option.isSome) = true := by native_decide
-- example : calculatePairing ((12 + 34 + 56) * g1) (78 * g2)
--           = calculatePairing (78 * g1) ((12 * g2) + (34 * g2)) * calculatePairing (78 * g1) (56 * g2) := by native_decide

-- theorem Residuals.mkTwo_orders_correctly {α} [LE α] [DecidableLE α] : ∀ (x₁ x₂ y₁ y₂ : α), Residues.mkTwo x₁ x₂ = .two y₁ y₂ → y₁ ≤ y₂ := by
--   intros x₁ x₂
--   simp [Residues.mkTwo]
--   match Hr₁ : decide (x₁ ≤ x₂), Hr₂ : decide (x₂ ≤ x₁) with
--   | true , _     => simp at *; intros; assumption
--   | false, true  => simp at *; intros; assumption
--   | false, false => simp

-- theorem Fq1.sqrtMod_some_le : ∀ (a x₁ x₂ : Fq1), Fq1.sqrtMod a = .two x₁ x₂ → x₁ ≤ x₂ := by
--   intros a x₁ x₂
--   simp [Fq1.sqrtMod]; split <;> try simp
--   apply Residuals.mkTwo_orders_correctly

-- example : Fq1.sqrtMod 4 = .two 2 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785 := by native_decide

-- example : Fq2.sqrtMod 4 = .two 2 (-2) := by native_decide
-- example :
--   (
--     let gx₁ := ⟨137029317603774969757902951708584054900881622716323587594561534433968645728174286358146752559144364991510801679554, 702688542154100195075240258442952241431821161159924394025502930672085343326590353077498141507579178214434502081315⟩
--     match Fq2.sqrtMod gx₁ with
--     | .two y₁ y₂ => y₁ * y₁ = gx₁ ∧ y₂ * y₂ = gx₁
--     | _          => false
--   ) = true := by native_decide

-- def testDst₁ := String.toByteList "QUUX-V01-CS02-with-expander-SHA256-128"

-- example : (expandMessageXmd [] testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
--         = "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235" := by native_decide
-- example : (expandMessageXmd (String.toByteList "abc") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
--         = "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615" := by native_decide
-- example : (expandMessageXmd (String.toByteList "abcdef0123456789") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
--         = "eff31487c770a893cfb36f912fbfcbff40d5661771ca4b2cb4eafe524333f5c1" := by native_decide
-- example : (expandMessageXmd (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
--         = "b23a1d2b4d97b2ef7785562a7e8bac7eed54ed6e97e29aa51bfe3f12ddad1ff9" := by native_decide
-- example : (expandMessageXmd (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
--         = "4623227bcc01293b8c130bf771da8c298dede7383243dc0993d2d94823958c4c" := by native_decide

-- example : (expandMessageXmd [] testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
--         = "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbee0d121587713a3e0dd4d5e69e93eb7cd4f5df4cd103e188cf60cb02edc3edf18eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dcc541708d3491184472c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced" := by native_decide
-- example : (expandMessageXmd (String.toByteList "abc") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
--         = "abba86a6129e366fc877aab32fc4ffc70120d8996c88aee2fe4b32d6c7b6437a647e6c3163d40b76a73cf6a5674ef1d890f95b664ee0afa5359a5c4e07985635bbecbac65d747d3d2da7ec2b8221b17b0ca9dc8a1ac1c07ea6a1e60583e2cb00058e77b7b72a298425cd1b941ad4ec65e8afc50303a22c0f99b0509b4c895f40" := by native_decide
-- example : (expandMessageXmd (String.toByteList "abcdef0123456789") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
--         = "ef904a29bffc4cf9ee82832451c946ac3c8f8058ae97d8d629831a74c6572bd9ebd0df635cd1f208e2038e760c4994984ce73f0d55ea9f22af83ba4734569d4bc95e18350f740c07eef653cbb9f87910d833751825f0ebefa1abe5420bb52be14cf489b37fe1a72f7de2d10be453b2c9d9eb20c7e3f6edc5a60629178d9478df" := by native_decide
-- example : (expandMessageXmd (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
--         = "80be107d0884f0d881bb460322f0443d38bd222db8bd0b0a5312a6fedb49c1bbd88fd75d8b9a09486c60123dfa1d73c1cc3169761b17476d3c6b7cbbd727acd0e2c942f4dd96ae3da5de368d26b32286e32de7e5a8cb2949f866a0b80c58116b29fa7fabb3ea7d520ee603e0c25bcaf0b9a5e92ec6a1fe4e0391d1cdbce8c68a" := by native_decide
-- example : (expandMessageXmd (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
--         = "546aff5444b5b79aa6148bd81728704c32decb73a3ba76e9e75885cad9def1d06d6792f8a7d12794e90efed817d96920d728896a4510864370c207f99bd4a608ea121700ef01ed879745ee3e4ceef777eda6d9e5e38b90c86ea6fb0b36504ba4a45d22e86f6db5dd43d98a294bebb9125d5b794e9d2a81181066eb954966a487" := by native_decide

-- def testDst₂ := String.toByteList "QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_"

-- theorem fieldPrime_le_pow_2_381 : fieldPrime ≤ 2 ^ 381 := by decide +native

-- def Fq1.pointToHexString : Point Fq1 → String
--   | .affine x y =>
--       let x' := Fin.castLE (fieldPrime_le_pow_2_381) x.t |> BitVec.ofFin |> BitVec.toHex
--       let y' := Fin.castLE (fieldPrime_le_pow_2_381) y.t |> BitVec.ofFin |> BitVec.toHex
--       s!"{x'} {y'}"
--   | .infinity   => "inf"

-- example : (Fq1.hashToCurve [] testDst₂ |> Option.get! |> Fq1.pointToHexString)
--         = "052926add2207b76ca4fa57a8734416c8dc95e24501772c814278700eed6d1e4e8cf62d9c09db0fac349612b759e79a1 08ba738453bfed09cb546dbb0783dbb3a5f1f566ed67bb6be0e8c67e2e81a4cc68ee29813bb7994998f3eae0c9c6a265" := by native_decide

-- example : (Fq1.hashToCurve (String.toByteList "abc") testDst₂ |> Option.get! |> Fq1.pointToHexString)
--         = "03567bc5ef9c690c2ab2ecdf6a96ef1c139cc0b2f284dca0a9a7943388a49a3aee664ba5379a7655d3c68900be2f6903 0b9c15f3fe6e5cf4211f346271d7b01c8f3b28be689c8429c85b67af215533311f0b8dfaaa154fa6b88176c229f2885d" := by native_decide

-- example : (Fq1.hashToCurve (String.toByteList "abcdef0123456789") testDst₂ |> Option.get! |> Fq1.pointToHexString)
--         = "11e0b079dea29a68f0383ee94fed1b940995272407e3bb916bbf268c263ddd57a6a27200a784cbc248e84f357ce82d98 03a87ae2caf14e8ee52e51fa2ed8eefe80f02457004ba4d486d6aa1f517c0889501dc7413753f9599b099ebcbbd2d709" := by native_decide

-- example : (Fq1.hashToCurve (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₂ |> Option.get! |> Fq1.pointToHexString)
--         = "15f68eaa693b95ccb85215dc65fa81038d69629f70aeee0d0f677cf22285e7bf58d7cb86eefe8f2e9bc3f8cb84fac488 1807a1d50c29f430b8cafc4f8638dfeeadf51211e1602a5f184443076715f91bb90a48ba1e370edce6ae1062f5e6dd38" := by native_decide

-- example : (Fq1.hashToCurve (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₂ |> Option.get! |> Fq1.pointToHexString)
--         = "082aabae8b7dedb0e78aeb619ad3bfd9277a2f77ba7fad20ef6aabdc6c31d19ba5a6d12283553294c1825c4b3ca2dcfe 05b84ae5a942248eea39e1d91030458c40153f3b654ab7872d779ad1e942856a20c438e8d99bc8abfbf74729ce1f7ac8" := by native_decide

-- def Fq2.pointToHexString : Point Fq2 → String
--   | .affine x y =>
--       let x₀ := Fin.castLE (fieldPrime_le_pow_2_381) x.u0.t |> BitVec.ofFin |> BitVec.toHex
--       let x₁ := Fin.castLE (fieldPrime_le_pow_2_381) x.u1.t |> BitVec.ofFin |> BitVec.toHex
--       let y₀ := Fin.castLE (fieldPrime_le_pow_2_381) y.u0.t |> BitVec.ofFin |> BitVec.toHex
--       let y₁ := Fin.castLE (fieldPrime_le_pow_2_381) y.u1.t |> BitVec.ofFin |> BitVec.toHex
--       s!"{x₀} + I * {x₁}; {y₀} + I * {y₁}"
--   | .infinity   => "inf"

-- def testDst₃ := String.toByteList "QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"

-- example : (Fq2.hashToCurve [] testDst₃ |> Option.get! |> Fq2.pointToHexString)
--          = "0141ebfbdca40eb85b87142e130ab689c673cf60f1a3e98d69335266f30d9b8d4ac44c1038e9dcdd5393faf5c41fb78a + I * 05cb8437535e20ecffaef7752baddf98034139c38452458baeefab379ba13dff5bf5dd71b72418717047f5b0f37da03d; "
--         ++ "0503921d7f6a12805e72940b963c0cf3471c7b2a524950ca195d11062ee75ec076daf2d4bc358c4b190c0c98064fdd92 + I * 12424ac32561493f3fe3c260708a12b7c620e7be00099a974e259ddc7d1f6395c3c811cdd19f1e8dbf3e9ecfdcbab8d6" := by native_decide

-- example : (Fq2.hashToCurve (String.toByteList "abc") testDst₃ |> Option.get! |> Fq2.pointToHexString)
--          = "02c2d18e033b960562aae3cab37a27ce00d80ccd5ba4b7fe0e7a210245129dbec7780ccc7954725f4168aff2787776e6 + I * 139cddbccdc5e91b9623efd38c49f81a6f83f175e80b06fc374de9eb4b41dfe4ca3a230ed250fbe3a2acf73a41177fd8; "
--         ++ "1787327b68159716a37440985269cf584bcb1e621d3a7202be6ea05c4cfe244aeb197642555a0645fb87bf7466b2ba48 + I * 00aa65dae3c8d732d10ecd2c50f8a1baf3001578f71c694e03866e9f3d49ac1e1ce70dd94a733534f106d4cec0eddd16" := by native_decide

-- example : (Fq2.hashToCurve (String.toByteList "abcdef0123456789") testDst₃ |> Option.get! |> Fq2.pointToHexString)
--          = "121982811d2491fde9ba7ed31ef9ca474f0e1501297f68c298e9f4c0028add35aea8bb83d53c08cfc007c1e005723cd0 + I * 190d119345b94fbd15497bcba94ecf7db2cbfd1e1fe7da034d26cbba169fb3968288b3fafb265f9ebd380512a71c3f2c; "
--         ++ "05571a0f8d3c08d094576981f4a3b8eda0a8e771fcdcc8ecceaf1356a6acf17574518acb506e435b639353c2e14827c8 + I * 0bb5e7572275c567462d91807de765611490205a941a5a6af3b1691bfe596c31225d3aabdf15faff860cb4ef17c7c3be" := by native_decide

-- example : (Fq2.hashToCurve (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₃ |> Option.get! |> Fq2.pointToHexString)
--          = "19a84dd7248a1066f737cc34502ee5555bd3c19f2ecdb3c7d9e24dc65d4e25e50d83f0f77105e955d78f4762d33c17da + I * 0934aba516a52d8ae479939a91998299c76d39cc0c035cd18813bec433f587e2d7a4fef038260eef0cef4d02aae3eb91; "
--         ++ "14f81cd421617428bc3b9fe25afbb751d934a00493524bc4e065635b0555084dd54679df1536101b2c979c0152d09192 + I * 09bcccfa036b4847c9950780733633f13619994394c23ff0b32fa6b795844f4a0673e20282d07bc69641cee04f5e5662" := by native_decide

-- example : (Fq2.hashToCurve (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₃ |> Option.get! |> Fq2.pointToHexString)
--          = "01a6ba2f9a11fa5598b2d8ace0fbe0a0eacb65deceb476fbbcb64fd24557c2f4b18ecfc5663e54ae16a84f5ab7f62534 + I * 11fca2ff525572795a801eed17eb12785887c7b63fb77a42be46ce4a34131d71f7a73e95fee3f812aea3de78b4d01569; "
--         ++ "0b6798718c8aed24bc19cb27f866f1c9effcdbf92397ad6448b5c9db90d2b9da6cbabf48adc1adf59a1a28344e79d57e + I * 03a47f8e6d1763ba0cad63d6114c0accbef65707825a511b251a660a9b3994249ae4e63fac38b23da0c398689ee2ab52" := by native_decide

theorem Residuals.mkTwo_orders_correctly {α} [LE α] [DecidableLE α] : ∀ (x₁ x₂ y₁ y₂ : α), Residues.mkTwo x₁ x₂ = .two y₁ y₂ → y₁ ≤ y₂ := by
  intros x₁ x₂
  simp [Residues.mkTwo]
  match Hr₁ : decide (x₁ ≤ x₂), Hr₂ : decide (x₂ ≤ x₁) with
  | true , _     => simp at *; intros; assumption
  | false, true  => simp at *; intros; assumption
  | false, false => simp

theorem Fq1.sqrtMod_some_le : ∀ (a x₁ x₂ : Fq1), Fq1.sqrtMod a = .two x₁ x₂ → x₁ ≤ x₂ := by
  intros a x₁ x₂
  simp [Fq1.sqrtMod]; split <;> try simp
  apply Residuals.mkTwo_orders_correctly

example : Fq1.sqrtMod 4 = .two 2 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785 := by native_decide

example : Fq2.sqrtMod 4 = .two 2 (-2) := by native_decide
example :
  (
    let gx₁ := ⟨137029317603774969757902951708584054900881622716323587594561534433968645728174286358146752559144364991510801679554, 702688542154100195075240258442952241431821161159924394025502930672085343326590353077498141507579178214434502081315⟩
    match Fq2.sqrtMod gx₁ with
    | .two y₁ y₂ => y₁ * y₁ = gx₁ ∧ y₂ * y₂ = gx₁
    | _          => false
  ) = true := by native_decide

def testDst₁ := String.toByteList "QUUX-V01-CS02-with-expander-SHA256-128"

example : (expandMessageXmd [] testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
        = "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235" := by native_decide
example : (expandMessageXmd (String.toByteList "abc") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
        = "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615" := by native_decide
example : (expandMessageXmd (String.toByteList "abcdef0123456789") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
        = "eff31487c770a893cfb36f912fbfcbff40d5661771ca4b2cb4eafe524333f5c1" := by native_decide
example : (expandMessageXmd (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
        = "b23a1d2b4d97b2ef7785562a7e8bac7eed54ed6e97e29aa51bfe3f12ddad1ff9" := by native_decide
example : (expandMessageXmd (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₁ 0x20 |> Option.get! |> uint8ListToHex)
        = "4623227bcc01293b8c130bf771da8c298dede7383243dc0993d2d94823958c4c" := by native_decide

example : (expandMessageXmd [] testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
        = "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbee0d121587713a3e0dd4d5e69e93eb7cd4f5df4cd103e188cf60cb02edc3edf18eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dcc541708d3491184472c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced" := by native_decide
example : (expandMessageXmd (String.toByteList "abc") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
        = "abba86a6129e366fc877aab32fc4ffc70120d8996c88aee2fe4b32d6c7b6437a647e6c3163d40b76a73cf6a5674ef1d890f95b664ee0afa5359a5c4e07985635bbecbac65d747d3d2da7ec2b8221b17b0ca9dc8a1ac1c07ea6a1e60583e2cb00058e77b7b72a298425cd1b941ad4ec65e8afc50303a22c0f99b0509b4c895f40" := by native_decide
example : (expandMessageXmd (String.toByteList "abcdef0123456789") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
        = "ef904a29bffc4cf9ee82832451c946ac3c8f8058ae97d8d629831a74c6572bd9ebd0df635cd1f208e2038e760c4994984ce73f0d55ea9f22af83ba4734569d4bc95e18350f740c07eef653cbb9f87910d833751825f0ebefa1abe5420bb52be14cf489b37fe1a72f7de2d10be453b2c9d9eb20c7e3f6edc5a60629178d9478df" := by native_decide
example : (expandMessageXmd (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
        = "80be107d0884f0d881bb460322f0443d38bd222db8bd0b0a5312a6fedb49c1bbd88fd75d8b9a09486c60123dfa1d73c1cc3169761b17476d3c6b7cbbd727acd0e2c942f4dd96ae3da5de368d26b32286e32de7e5a8cb2949f866a0b80c58116b29fa7fabb3ea7d520ee603e0c25bcaf0b9a5e92ec6a1fe4e0391d1cdbce8c68a" := by native_decide
example : (expandMessageXmd (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₁ 0x80 |> Option.get! |> uint8ListToHex)
        = "546aff5444b5b79aa6148bd81728704c32decb73a3ba76e9e75885cad9def1d06d6792f8a7d12794e90efed817d96920d728896a4510864370c207f99bd4a608ea121700ef01ed879745ee3e4ceef777eda6d9e5e38b90c86ea6fb0b36504ba4a45d22e86f6db5dd43d98a294bebb9125d5b794e9d2a81181066eb954966a487" := by native_decide

def testDst₂ := String.toByteList "QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_"

theorem fieldPrime_le_pow_2_381 : fieldPrime ≤ 2 ^ 381 := by decide +native

def Fq1.pointToHexString : Point Fq1 → String
  | .affine x y =>
      let x' := Fin.castLE (fieldPrime_le_pow_2_381) x.t |> BitVec.ofFin |> BitVec.toHex
      let y' := Fin.castLE (fieldPrime_le_pow_2_381) y.t |> BitVec.ofFin |> BitVec.toHex
      s!"{x'} {y'}"
  | .infinity   => "inf"

example : (Fq1.hashToCurve [] testDst₂ |> Option.get! |> Fq1.pointToHexString)
        = "052926add2207b76ca4fa57a8734416c8dc95e24501772c814278700eed6d1e4e8cf62d9c09db0fac349612b759e79a1 08ba738453bfed09cb546dbb0783dbb3a5f1f566ed67bb6be0e8c67e2e81a4cc68ee29813bb7994998f3eae0c9c6a265" := by native_decide

example : (Fq1.hashToCurve (String.toByteList "abc") testDst₂ |> Option.get! |> Fq1.pointToHexString)
        = "03567bc5ef9c690c2ab2ecdf6a96ef1c139cc0b2f284dca0a9a7943388a49a3aee664ba5379a7655d3c68900be2f6903 0b9c15f3fe6e5cf4211f346271d7b01c8f3b28be689c8429c85b67af215533311f0b8dfaaa154fa6b88176c229f2885d" := by native_decide

example : (Fq1.hashToCurve (String.toByteList "abcdef0123456789") testDst₂ |> Option.get! |> Fq1.pointToHexString)
        = "11e0b079dea29a68f0383ee94fed1b940995272407e3bb916bbf268c263ddd57a6a27200a784cbc248e84f357ce82d98 03a87ae2caf14e8ee52e51fa2ed8eefe80f02457004ba4d486d6aa1f517c0889501dc7413753f9599b099ebcbbd2d709" := by native_decide

example : (Fq1.hashToCurve (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₂ |> Option.get! |> Fq1.pointToHexString)
        = "15f68eaa693b95ccb85215dc65fa81038d69629f70aeee0d0f677cf22285e7bf58d7cb86eefe8f2e9bc3f8cb84fac488 1807a1d50c29f430b8cafc4f8638dfeeadf51211e1602a5f184443076715f91bb90a48ba1e370edce6ae1062f5e6dd38" := by native_decide

example : (Fq1.hashToCurve (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₂ |> Option.get! |> Fq1.pointToHexString)
        = "082aabae8b7dedb0e78aeb619ad3bfd9277a2f77ba7fad20ef6aabdc6c31d19ba5a6d12283553294c1825c4b3ca2dcfe 05b84ae5a942248eea39e1d91030458c40153f3b654ab7872d779ad1e942856a20c438e8d99bc8abfbf74729ce1f7ac8" := by native_decide

def Fq2.pointToHexString : Point Fq2 → String
  | .affine x y =>
      let x₀ := Fin.castLE (fieldPrime_le_pow_2_381) x.u0.t |> BitVec.ofFin |> BitVec.toHex
      let x₁ := Fin.castLE (fieldPrime_le_pow_2_381) x.u1.t |> BitVec.ofFin |> BitVec.toHex
      let y₀ := Fin.castLE (fieldPrime_le_pow_2_381) y.u0.t |> BitVec.ofFin |> BitVec.toHex
      let y₁ := Fin.castLE (fieldPrime_le_pow_2_381) y.u1.t |> BitVec.ofFin |> BitVec.toHex
      s!"{x₀} + I * {x₁}; {y₀} + I * {y₁}"
  | .infinity   => "inf"

def testDst₃ := String.toByteList "QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_"

example : (Fq2.hashToCurve [] testDst₃ |> Option.get! |> Fq2.pointToHexString)
         = "0141ebfbdca40eb85b87142e130ab689c673cf60f1a3e98d69335266f30d9b8d4ac44c1038e9dcdd5393faf5c41fb78a + I * 05cb8437535e20ecffaef7752baddf98034139c38452458baeefab379ba13dff5bf5dd71b72418717047f5b0f37da03d; "
        ++ "0503921d7f6a12805e72940b963c0cf3471c7b2a524950ca195d11062ee75ec076daf2d4bc358c4b190c0c98064fdd92 + I * 12424ac32561493f3fe3c260708a12b7c620e7be00099a974e259ddc7d1f6395c3c811cdd19f1e8dbf3e9ecfdcbab8d6" := by native_decide

example : (Fq2.hashToCurve (String.toByteList "abc") testDst₃ |> Option.get! |> Fq2.pointToHexString)
         = "02c2d18e033b960562aae3cab37a27ce00d80ccd5ba4b7fe0e7a210245129dbec7780ccc7954725f4168aff2787776e6 + I * 139cddbccdc5e91b9623efd38c49f81a6f83f175e80b06fc374de9eb4b41dfe4ca3a230ed250fbe3a2acf73a41177fd8; "
        ++ "1787327b68159716a37440985269cf584bcb1e621d3a7202be6ea05c4cfe244aeb197642555a0645fb87bf7466b2ba48 + I * 00aa65dae3c8d732d10ecd2c50f8a1baf3001578f71c694e03866e9f3d49ac1e1ce70dd94a733534f106d4cec0eddd16" := by native_decide

example : (Fq2.hashToCurve (String.toByteList "abcdef0123456789") testDst₃ |> Option.get! |> Fq2.pointToHexString)
         = "121982811d2491fde9ba7ed31ef9ca474f0e1501297f68c298e9f4c0028add35aea8bb83d53c08cfc007c1e005723cd0 + I * 190d119345b94fbd15497bcba94ecf7db2cbfd1e1fe7da034d26cbba169fb3968288b3fafb265f9ebd380512a71c3f2c; "
        ++ "05571a0f8d3c08d094576981f4a3b8eda0a8e771fcdcc8ecceaf1356a6acf17574518acb506e435b639353c2e14827c8 + I * 0bb5e7572275c567462d91807de765611490205a941a5a6af3b1691bfe596c31225d3aabdf15faff860cb4ef17c7c3be" := by native_decide

example : (Fq2.hashToCurve (String.toByteList "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq") testDst₃ |> Option.get! |> Fq2.pointToHexString)
         = "19a84dd7248a1066f737cc34502ee5555bd3c19f2ecdb3c7d9e24dc65d4e25e50d83f0f77105e955d78f4762d33c17da + I * 0934aba516a52d8ae479939a91998299c76d39cc0c035cd18813bec433f587e2d7a4fef038260eef0cef4d02aae3eb91; "
        ++ "14f81cd421617428bc3b9fe25afbb751d934a00493524bc4e065635b0555084dd54679df1536101b2c979c0152d09192 + I * 09bcccfa036b4847c9950780733633f13619994394c23ff0b32fa6b795844f4a0673e20282d07bc69641cee04f5e5662" := by native_decide

example : (Fq2.hashToCurve (String.toByteList "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") testDst₃ |> Option.get! |> Fq2.pointToHexString)
         = "01a6ba2f9a11fa5598b2d8ace0fbe0a0eacb65deceb476fbbcb64fd24557c2f4b18ecfc5663e54ae16a84f5ab7f62534 + I * 11fca2ff525572795a801eed17eb12785887c7b63fb77a42be46ce4a34131d71f7a73e95fee3f812aea3de78b4d01569; "
        ++ "0b6798718c8aed24bc19cb27f866f1c9effcdbf92397ad6448b5c9db90d2b9da6cbabf48adc1adf59a1a28344e79d57e + I * 03a47f8e6d1763ba0cad63d6114c0accbef65707825a511b251a660a9b3994249ae4e63fac38b23da0c398689ee2ab52" := by native_decide

end Tests

end Cryptograph.BLS12_381
