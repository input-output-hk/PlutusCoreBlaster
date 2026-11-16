use aiken/collection/list

pub fn sum_if_asset(xs: List<Pair<ByteArray, Int>>, asset: ByteArray) -> Int {
  list.foldl(xs, 0, fn(pair, acc) {
    let Pair(key, quantity) = pair
    if key == asset { acc + quantity } else { acc }
  })
}
