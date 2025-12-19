import Cryptograph.BLS12_381.Basic

namespace Cryptograph.BLS12_381

open Cryptograph.BLS12_381.Internal

theorem g1_times_groupOrder : pointMul groupOrder g1 = .infinity := by native_decide
theorem g2_times_groupOrder : pointMul groupOrder g2 = .infinity := by native_decide

namespace Tests

example : pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218 g1 =
  .affine 0x019906b4953328ec688ffc9e41ea7d79d295c7de6249eb0397680306c5fe3aa3bbb45324bdbc379e8e4116166f2a0d40
          0x165f11693959e7193af31b99b724f95d7b49baa2394b758c2455ef725f32abd56361e1e151f2bbd7a7efc6f3bb5652d4 := by native_decide

example : pointMul 0x49abcbaa08d87d1cba8fd9c0ea04df30b94df934827a7383098ac39e1aafc218 g2 =
  .affine { u1 := 0x02433912fa403e0d19d39c7687eb1041f474a82fdd646b1a35afb4d088f11469467468f1ba16c3e5838503919bdbfa24
          , u0 := 0x14906db96db027e17449a1323198cfccde4d15456ce09f3fef4c7baed5495463b7cc750300e0e2918d5680d97a567122 }
          { u1 := 0x0e82e52250625e4c0864645fba3b36e24c36dbc3d4bae0ca40b0c28b0e3780bf6b8d022c032727e8195e2a2b547be84b
          , u0 := 0x0f240b0ffee3ac62cd5576f012a92cd78c9ded14c11c7637caff4daf885c9a258783a7aef4dc1815737a5b606e03868e } := by native_decide

example : (31 * g1) + (-21 * g1) = pointMul 10 g1 := by native_decide
example : (31 * g1) + (-30 * g1) =             g1 := by native_decide
example : (31 * g2) + (-21 * g2) = pointMul 10 g2 := by native_decide
example : (31 * g2) + (-30 * g2) =             g2 := by native_decide

def p1 : Point Fq1 :=
  .affine 0x14ade5f375a7e7194bf5244ace032817f63ff854f22654e3c0855511156fe98ba5c092ad9d68011f783e0f418619b2f2
          0x0b54adeba0fdaeeaec7a7146c738c7ebf3f44158475541427ce976fe020e52dedd97feba12c7272b8f3dc49a7d122f8d

example : isOnCurve    p1 = true := by native_decide
example : isInSubGroup p1 = true := by native_decide

def q1 : Point Fq2 :=
  .affine { u1 := 0x14ebc73c50a68b2333c169565ab75e35c03caaae6573884db2557a6731eca4c643bf7156cb6a2fee60b079577d4732e6
          , u0 := 0x064974dc7ff588a0b38e37da6b767b91d068924526dd8698f131b6f19b309065aab861b33411675781d9d42b63935c85 }
          { u1 := 0x16048641e0249a5ff6cb1b4a8c9194589148c1903b800752d8a6c09867508952d14fecb015cc4f337372b29bc32b08b1
          , u0 := 0x172f08bfdf8fca06c461c9978e8d8f7de5126a9ee74d086a82d90545d9180e3f9199a7fd2fbd022a9bcfa833ec321e0a }

example : isOnCurve    q1 = true := by native_decide
example : isInSubGroup q1 = true := by native_decide

def p2 : Point Fq1 :=
  .affine 0x19097e1378ae74067593c7e6b71fc8ec41d11e8e1b67b9ca47475e2eb02d5959cfb4bb09a3cb4c7fc14506629b4176d1
          0x0e41648923fc4a39b9e0e0f3d4b0fdcae45caad07622e2d40e67d2eea13bff92f071c0cf4b6687417efdadfae4fec00a

example : isOnCurve    p2 = true := by native_decide
example : isInSubGroup p2 = true := by native_decide

def q2 : Point Fq2 :=
  .affine { u1 := 0x0da18340291cbdd3cfaf596d62fe88f4cf211e8a2439f736786c12fba4e66cccb9279ef1a814d81785bec778c60f9284
          , u0 := 0x0a1d6930cfb119d6b2c52f8260217bf7859437e6aa8b8ca891ce74886f7c667274507b6f107a0c4c7618fe2f3571fcb2 }
          { u1 := 0x009745aac53daa7296110ad436829ec3cfd8fbc83012878608479a11caf2ada57c95dd64fd5fd3d4cf3cdf536defd288
          , u0 := 0x1831856291ad777b5e8f2eff3c2a4efe23a56f44ad97cda5c77f5a9c51bef1e13691011ab1979568363f5b1fecdd32d6 }

example : isOnCurve    q2 = true := by native_decide
example : isInSubGroup q2 = true := by native_decide

example : (calculatePairing p1 q1 |> Option.isSome) = true := by native_decide
example : calculatePairing p1 q1 = calculatePairing p2 q2 := by native_decide

example : calculatePairing (123 * g1) (3224 * g2) = calculatePairing (3224 * g1) (123 * g2) := by native_decide

example : (calculatePairing (((12 + 34) * 56) * g1) (78 * g2) |> Option.isSome) = true := by native_decide
example : calculatePairing (((12 + 34) * 56) * g1) (78 * g2) =
          (· * ·) <$> calculatePairing (78 * g1) ((12 * 56) * g2)
                  <*> calculatePairing (78 * g1) ((34 * 56) * g2) := by native_decide

example : (calculatePairing ((12 + 34 + 56) * g1) (78 * g2) |> Option.isSome) = true := by native_decide
example : calculatePairing ((12 + 34 + 56) * g1) (78 * g2) =
          (· * ·) <$> calculatePairing (78 * g1) ((12 * g2) + (34 * g2))
                  <*> calculatePairing (78 * g1) (56 * g2) := by native_decide

end Tests

end Cryptograph.BLS12_381
