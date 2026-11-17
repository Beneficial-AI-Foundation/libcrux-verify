import LibcruxHmac.Formal.Specs.Defs.Hmac

/-!
# Known-answer checks for the reference definitions

`#guard` checks of `Defs/Sha2.lean` and `Defs/Hmac.lean` against test vectors.
They are evaluated when this file is built; they add no declarations and no axioms.

* SHA-2: NIST CAVP vectors from `crates/testing/kats/tv/sha2/SHA{256,384,512}ShortMsg.rsp`.
  The lengths are chosen around the padding boundaries: one or two padded blocks.
* HMAC: Wycheproof vectors with full-length tags from
  `crates/testing/kats/wycheproof/hmac_sha{256,384,512}_test.json` (by `tcId`).
  SHA-256 `tcId` 169 has a 65-byte key, longer than the block, so it checks the
  hash-the-key branch of `keyBlock`.
* RFC 4231 §4.7 (test case 6, a 131-byte key) checks that branch for all three
  hashes. These are the published RFC values. They are not in the repository, so
  only the RFC itself can confirm them.
* Output lengths: each hash and each HMAC has its nominal length, and
  `tagLength alg` is the length of `hmacOf alg`.
* The split form used by HACL: whole blocks first (`update_nblocks`), then the
  final chunk padded for the total length (`update_last`), as in
  `compute_sha2_*` and `hash_*`, gives the same result as the hash of the whole.
-/

open Aeneas Aeneas.Std

namespace libcrux_hmac.Spec.Kat

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

/-- The bytes written by a string of hexadecimal digits. -/
def hex (s : String) : List Byte :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i =>
    byte (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)

/-! ## SHA-2 (NIST CAVP) -/

-- SHA256ShortMsg.rsp, Len = 0
#guard sha256 (hex "") =
  hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

-- SHA256ShortMsg.rsp, Len = 8
#guard sha256 (hex "d3") =
  hex "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1"

-- SHA256ShortMsg.rsp, Len = 440
#guard sha256 (hex ("3ebfb06db8c38d5ba037f1363e118550aad94606e26835a01af05078533cc25f2f39573c" ++
               "04b632f62f68c294ab31f2a3e2a1a0d8c2be51")) =
  hex "6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4"

-- SHA256ShortMsg.rsp, Len = 448
#guard sha256 (hex ("2d52447d1244d2ebc28650e7b05654bad35b3a68eedc7f8515306b496d75f3e73385dd1b" ++
               "002625024b81a02f2fd6dffb6e6d561cb7d0bd7a")) =
  hex "cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360"

-- SHA256ShortMsg.rsp, Len = 512
#guard sha256 (hex ("5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a6505472" ++
               "08251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509")) =
  hex "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa"

-- SHA384ShortMsg.rsp, Len = 0
#guard sha384 (hex "") =
  hex ("38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebf" ++
      "e76f65fbd51ad2f14898b95b")

-- SHA384ShortMsg.rsp, Len = 888
#guard sha384 (hex ("a04f390a9cc2effad05db80d9076a8d4b6cc8bba97b27b423670b290b8e69c2b18723001" ++
               "1c1481ac88d090f39154659494db5e410851c6e8b2b8a93717cae76037e0881978124fe7" ++
               "e1a0929d8891491f4e99646cc94062dc82411fa66130eda46560e75b9804823643946512" ++
               "5e737b")) =
  hex ("e7089d72945cef851e689b4409cfb63d135f0b5cdfb0dac6c3a292dd70371ab4b79da199" ++
      "7d7992906ac7213502662920")

-- SHA384ShortMsg.rsp, Len = 896
#guard sha384 (hex ("f419494c3c6d0727b3395a483a2167182a7252f4fd099c2d4b71b053f94bb8b3adf3b51e" ++
               "8460cfec084ce9415c95798fbae4975c208c544645b54c44d2b97f2ecfce5c805be61f5b" ++
               "a1d35dcc07afdd51a87baa990506668cf710e18be9b0ebf943f366fa29c69f7a6616de72" ++
               "a3353b66")) =
  hex ("aead8688c58c6ba4e9cadb4756b465dce0fb06f1cfaa478197f2ea89414e47e9572034ad" ++
      "fed160703c79b82b3fd7ab78")

-- SHA384ShortMsg.rsp, Len = 1024
#guard sha384 (hex ("3bf52cc5ee86b9a0190f390a5c0366a560b557000dbe5115fd9ee11630a62769011575f1" ++
               "5881198f227876e8fe685a6939bc8b89fd48a34ec5e71e131462b2886794dffa68ccc6d5" ++
               "64733e67ffef25e627c6f4b5460796e3bce67bf58ca6e8e555bc916a8531697ac948b90d" ++
               "c8616f25101db90b50c3d3dbc9e21e42ff387187")) =
  hex ("12b6cb35eda92ee37356ddee77781a17b3d90e563824a984faffc6fdd1693bd762603963" ++
      "5563cfc3b9a2b00f9c65eefd")

-- SHA512ShortMsg.rsp, Len = 0
#guard sha512 (hex "") =
  hex ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c" ++
      "5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")

-- SHA512ShortMsg.rsp, Len = 888
#guard sha512 (hex ("324533e685f1852e358eea8ea8b81c288b3f3beb1f2bc2b8d3fdbac318382e3d7120de30" ++
               "c9c237aa0a34831deb1e5e060a7969cd3a9742ec1e64b354f7eb290cba1c681c66cc7ea9" ++
               "94fdf5614f604d1a2718aab581c1c94931b1387e4b7dc73635bf3a7301174075fa70a922" ++
               "7d85d3")) =
  hex ("3b26c5170729d0814153becb95f1b65cd42f9a6d0649d914e4f69d938b5e9dc041cd0f5c" ++
      "8da0b484d7c7bc7b1bdefb08fe8b1bfedc81109345bc9e9a399feedf")

-- SHA512ShortMsg.rsp, Len = 896
#guard sha512 (hex ("518985977ee21d2bf622a20567124fcbf11c72df805365835ab3c041f4a9cd8a0ad63c9d" ++
               "ee1018aa21a9fa3720f47dc48006f1aa3dba544950f87e627f369bc2793ede2122327449" ++
               "2cceb77be7eea50e5a509059929a16d33a9f54796cde5770c74bd3ecc25318503f1a4197" ++
               "6407aff2")) =
  hex ("c00926a374cde55b8fbd77f50da1363da19744d3f464e07ce31794c5a61b6f9c85689fa1" ++
      "cfe136553527fd876be91673c2cac2dd157b2defea360851b6d92cf4")

-- SHA512ShortMsg.rsp, Len = 1024
#guard sha512 (hex ("fd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e40" ++
               "97f9d3bb4e9fbf97186e0db6db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a" ++
               "2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c7d2480e8e82bce175540bdfa" ++
               "d7752bc95b577f229515394f3ae5cec870a4b2f8")) =
  hex ("a21b1077d52b27ac545af63b32746c6e3c51cb0cb9f281eb9f3580a6d4996d5c9917d2a6" ++
      "e484627a9d5a06fa1b25327a9d710e027387fc3e07d7c4d14c6086cc")

/-! ## HMAC (Wycheproof) -/

-- hmac_sha256_test.json, tcId 1
#guard hmacSha256
    (hex "1e225cafb90339bba1b24076d4206c3e79c355805d851682bc818baa4f5a7779")
    (hex "") =
  hex "b175b57d89ea6cb606fb3363f2538abd73a4c00b4a1386905bac809004cf1933"

-- hmac_sha256_test.json, tcId 2
#guard hmacSha256
    (hex "8159fd15133cd964c9a6964c94f0ea269a806fd9f43f0da58b6cd1b33d189b2a")
    (hex "77") =
  hex "dfc5105d5eecf7ae7b8b8de3930e7659e84c4172f2555142f1e568fc1872ad93"

-- hmac_sha256_test.json, tcId 24
#guard hmacSha256
    (hex "23209b7c5aadcbd13f7279af1a86d3c7ae8f179d1bcaaad0dff9a15302e78dbf")
    (hex ("84bdac37e1af35d9356404e2787d47ece58348dea76a4a46e8aade3463d4db8c94a051be" ++
         "3733b38d756984865d56c60e8025f15e3f968f093e7fb7ebc7e31189c5692d15ed425673" ++
         "7b9b1894e5809503aaa1c9983fb096aa21916361eeb6ef455b129723a1a1ddf9deddea20" ++
         "8529a648")) =
  hex "4a85c479d1650dbd73bc5248074a55ff50218bddaa8d1fddaaf44946dc19aefb"

-- hmac_sha256_test.json, tcId 163
#guard hmacSha256
    (hex "a349ac0a9f9f74e48e099cc3dbf9a9c9")
    (hex "") =
  hex "3a8437b877b75cc08a4d8d7559a8fc6869a58c713da63d1d4b350d59b597e30c"

-- hmac_sha256_test.json, tcId 169
#guard hmacSha256
    (hex ("8a0c46eb8a2959e39865330079763341e7439dab149694ee57e0d61ec73d947e1d5301cd" ++
         "974e18a5e0d1cf0d2c37e8aadd9fd589d57ef32e47024a99bc3f70c077"))
    (hex "") =
  hex "f5bfb940561fb4db73ebba49bf2e4893bb0cca618a71b7ecf6aca38231e167ea"

-- hmac_sha384_test.json, tcId 1
#guard hmacSha384
    (hex ("ee8df067857df2300fa71a10c30997178bb3796127b5ece5f2ccc170932be0e78ea9b0a5" ++
         "936c09157e671ce7ec9fc510"))
    (hex "") =
  hex ("a655184daf3346ffc6629d493c8442644e4996a2799e42e3306fa6f5b0967b6cf3a6f819" ++
      "bab89bce297d1d1a5907b2d0")

-- hmac_sha384_test.json, tcId 2
#guard hmacSha384
    (hex ("976696c0dc97182ca771975c3928ff9168ef89cd740cd2292858fd916068a702bc1df7c6" ++
         "cd8ee1f0d25e61d4c514cc5d"))
    (hex "2b") =
  hex ("363e8973fedcf7892013dfae0b7065d61d80b98c635bc09ed860a01473b9bcd0dc550dbf" ++
      "66cf0d601fe9cbf3ae59620d")

-- hmac_sha384_test.json, tcId 24
#guard hmacSha384
    (hex ("dc770c64d00d156e43cb74970e3a1a2ad28b6d9ec6b2b6e5ac3e356a99f879cb620f0034" ++
         "0c044cc1f31bdccfa0dbd177"))
    (hex ("403fd8e3ef51b6539db658a894be85b58fbc84881e61c5e0cb13ae421a09d31d78060325" ++
         "6d390edd056d190856be00ad20a7048f0c67416fe8e02884086155f4263262e8c1275504" ++
         "d4f91f2751d3c3dccd4409ff2b45e41de93f7b104d58f6e15bacb62ace9700615ecc1b30" ++
         "a0cc1b35")) =
  hex ("1c4f6474f39e6eabbe7a99faa234f49833444130acf01dae68d68251a930419960b0fb5f" ++
      "48360149e05d1209941cc9ec")

-- hmac_sha384_test.json, tcId 163
#guard hmacSha384
    (hex "08476e9d49499c5f52e37f80ece6f5a45459948806b48241")
    (hex "") =
  hex ("1b6cfc8709aab8075465f32e13b0b0f796cc34d93d7bed090f297dcf9fb75e0d8e285b15" ++
      "00b732d554ac97ba45f33e47")

-- hmac_sha384_test.json, tcId 169
#guard hmacSha384
    (hex ("db6f9956c3f4ca6e41f1f7f14629d44c79e0353edbf3e310e6858bbc45a7cd57778a9053" ++
         "ba22a141bf58bfd434ad08648c7041a224b97a0d17e0edf94fd40b410a"))
    (hex "") =
  hex ("0cb1b296255bb259f3b601b49b35524a5eca6c52360754d3d96dd521c905b1c1821d7496" ++
      "5967d8e86d50de950fe4d635")

-- hmac_sha512_test.json, tcId 1
#guard hmacSha512
    (hex ("5365244bb43f23f18dfc86c09d62db4741138bec1fbddc282d295e0a098eb5c3e37bd6f4" ++
         "cc16d5ce7d77b1d474a1eb4db313cc0c24e48992ac125196549df9a8"))
    (hex "") =
  hex ("d0a556bd1afa8df1ebf9e3ee683a8a2450a7c83eba2daf2e2ff2f953f0cd64da216e6713" ++
      "4cf55578b205c8a1e241ba1369516a5ef4298b9c1d31e9d59fc04fe4")

-- hmac_sha512_test.json, tcId 2
#guard hmacSha512
    (hex ("00698977f7102c67b594166919aa99dc3e58c7b6697a6422e238d04d2f57b2c74e4e84f5" ++
         "c4c6b792952df72f1c09244802f0bcf8752efb90e836110703bfa21c"))
    (hex "01") =
  hex ("4d1609cc2c2f1ab5ddc35815ae1b5dc046f226bde17ec37a4c89ec46fbd31af2aeb810b1" ++
      "96dffdd11924d3772bef26a7a542e0a1673b76b915d41cbd3df0f6a6")

-- hmac_sha512_test.json, tcId 24
#guard hmacSha512
    (hex ("1e981d0cbbad5bea9480d836b4704bf3147663b6ea59e1e0a280fb45d9b85d445dc97215" ++
         "9dde301c6f1e66681f95642dbb9a9218c00d0cd724cb02f3bcaea2ea"))
    (hex ("440dff390688c9fde31c17fdb61c1d13899f9544a986324c34d5eb07bef9a4436297f4a7" ++
         "fe16de5dd7b24e0c7c129051efe6f2dd0a21aec05c3e3c8f6fa30d9c0cbd60d840d14f0b" ++
         "2a928bc7189b9de4a6a731151d6b31e6a0ecae75095434737be8c3db11a6a697d0616c78" ++
         "b97041de")) =
  hex ("c52eb5d18e90687248342a84dc0241c680e992b88b1409275df7e347c99169a50cd780eb" ++
      "4726ad759e2a027fb091354e3d7c7aba8a21f8acd1d0e21236af5f98")

-- hmac_sha512_test.json, tcId 163
#guard hmacSha512
    (hex "14d93759fc28f3319ab74b8167c974e800f032344dc2747ec0f4945061a47827")
    (hex "") =
  hex ("68934dbe948d9a77a5e0a92ed98254fa3b6c93c8bf5eeaa912b7dfdf762b37192c5d8523" ++
      "bcab9ad71b09bf96d8454188d001c7f2077eb641199f5731b9f94669")

-- hmac_sha512_test.json, tcId 169
#guard hmacSha512
    (hex ("dd1e0bdbb6b60862176484f3669da531455f1cd714f999c29f08b851055fee8d72186d37" ++
         "6c236f4e16cba7a25cba879fb2753deca4459aaebc6f6de625d99af330"))
    (hex "") =
  hex ("7e4f7d844b3ba0e025b66de7cc6227bc50d4e174930251bfff3df36c3900b5b76b00095a" ++
      "896d0f96842e37b6134df40760307699534d6670f138974ee1c58d94")

/-! ## HMAC (RFC 4231 §4.7, test case 6) -/

/-- The RFC 4231 test case 6 key: 131 bytes `0xaa`. -/
def rfc4231Key : List Byte := List.replicate 131 (byte 0xaa)

/-- The RFC 4231 test case 6 data. -/
def rfc4231Data : List Byte :=
  "Test Using Larger Than Block-Size Key - Hash Key First".toList.map (byte ·.toNat)

#guard hmacSha256 rfc4231Key rfc4231Data =
  hex "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"

#guard hmacSha384 rfc4231Key rfc4231Data =
  hex ("4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab" ++
      "4030fe8296248df163f44952")

#guard hmacSha512 rfc4231Key rfc4231Data =
  hex ("80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037" ++
      "e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598")

/-! ## Output lengths -/

#guard (sha256 []).length = 32 && (sha384 []).length = 48 && (sha512 []).length = 64
#guard (hmacOf .Sha256 [] []).length = tagLength .Sha256
#guard (hmacOf .Sha384 [] []).length = tagLength .Sha384
#guard (hmacOf .Sha512 [] []).length = tagLength .Sha512
#guard (hmacOf .Sha256 rfc4231Key rfc4231Data).length = tagLength .Sha256

/-! ## The split form used by HACL (`update_nblocks`, then `update_last`) -/

/-- The hash of `m` computed in the HACL shape: the first `k` whole blocks with
`compressBlocks` (`update_nblocks`), then the rest of `m` with `padTail` for the
total length `m.length` (`update_last`). -/
def splitHash (p : Sha2Core) (IV : List (BitVec p.w)) (outLen k : Nat) (m : List Byte) :
    List Byte :=
  let H := p.compressBlocks IV (m.take (k * p.blockLen))
  (p.serialize (p.compressBlocks H (p.padTail m.length (m.drop (k * p.blockLen))))).take outLen

/-- The bytes `0, 1, …, n - 1` (mod 256). -/
def bytesUpTo (n : Nat) : List Byte := (List.range n).map byte

-- A final chunk of exactly one block: empty data (the `ipad` block alone), and
-- data whose length is a multiple of the block.
#guard splitHash sha256Core sha256IV 32 0 (bytesUpTo 64) = sha256 (bytesUpTo 64)
#guard splitHash sha256Core sha256IV 32 1 (bytesUpTo 128) = sha256 (bytesUpTo 128)
#guard splitHash sha512Core sha384IV 48 0 (bytesUpTo 128) = sha384 (bytesUpTo 128)
#guard splitHash sha512Core sha384IV 48 1 (bytesUpTo 256) = sha384 (bytesUpTo 256)
#guard splitHash sha512Core sha512IV 64 0 (bytesUpTo 128) = sha512 (bytesUpTo 128)
#guard splitHash sha512Core sha512IV 64 1 (bytesUpTo 256) = sha512 (bytesUpTo 256)
-- A partial final chunk after one block (the total length differs from the chunk's).
#guard splitHash sha256Core sha256IV 32 1 (bytesUpTo 100) = sha256 (bytesUpTo 100)
#guard splitHash sha512Core sha384IV 48 1 (bytesUpTo 200) = sha384 (bytesUpTo 200)
#guard splitHash sha512Core sha512IV 64 1 (bytesUpTo 200) = sha512 (bytesUpTo 200)
-- The outer hash: the `opad` block, then the inner digest as the final chunk.
#guard splitHash sha256Core sha256IV 32 1 (bytesUpTo 96) = sha256 (bytesUpTo 96)
#guard splitHash sha512Core sha384IV 48 1 (bytesUpTo 176) = sha384 (bytesUpTo 176)
#guard splitHash sha512Core sha512IV 64 1 (bytesUpTo 192) = sha512 (bytesUpTo 192)
-- Several whole blocks before a partial chunk.
#guard splitHash sha256Core sha256IV 32 3 (bytesUpTo 230) = sha256 (bytesUpTo 230)
#guard splitHash sha512Core sha512IV 64 2 (bytesUpTo 300) = sha512 (bytesUpTo 300)

end libcrux_hmac.Spec.Kat
