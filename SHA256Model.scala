import java.math.BigInteger

import scala.collection.mutable.ListBuffer

case class Constant(
                     h: Seq[BigInt] = Seq(
                       // Initialize hash states:
                       // first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19:
                       "6a09e667", "bb67ae85", "3c6ef372", "a54ff53a", "510e527f", "9b05688c", "1f83d9ab", "5be0cd19").map(BigInt(_, 16)),
                     k: Seq[BigInt] = Seq(
                       // Initialize array of round constants:
                       // first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311:
                       "428a2f98", "71374491", "b5c0fbcf", "e9b5dba5", "3956c25b", "59f111f1", "923f82a4", "ab1c5ed5",
                       "d807aa98", "12835b01", "243185be", "550c7dc3", "72be5d74", "80deb1fe", "9bdc06a7", "c19bf174",
                       "e49b69c1", "efbe4786", "0fc19dc6", "240ca1cc", "2de92c6f", "4a7484aa", "5cb0a9dc", "76f988da",
                       "983e5152", "a831c66d", "b00327c8", "bf597fc7", "c6e00bf3", "d5a79147", "06ca6351", "14292967",
                       "27b70a85", "2e1b2138", "4d2c6dfc", "53380d13", "650a7354", "766a0abb", "81c2c92e", "92722c85",
                       "a2bfe8a1", "a81a664b", "c24b8b70", "c76c51a3", "d192e819", "d6990624", "f40e3585", "106aa070",
                       "19a4c116", "1e376c08", "2748774c", "34b0bcb5", "391c0cb3", "4ed8aa4a", "5b9cca4f", "682e6ff3",
                       "748f82ee", "78a5636f", "84c87814", "8cc70208", "90befffa", "a4506ceb", "bef9a3f7", "c67178f2").map(BigInt(_, 16)))

class SHA256CTX(iv: Seq[BigInt], messageBlock: Seq[BigInt], state: Seq[BigInt], round: Int) {

  def _rotr(x: BigInt, y: Int): BigInt = {
    ((x >> y) | (x << (32 - y))) & BigInt("ffffffff", 16)
  }

  // sanity check
  iv.foreach(x => require(x < BigInt("ffffffff", 16)))
  messageBlock.foreach(x => require(x < BigInt("ffffffff", 16)))
  state.foreach(x => require(x < BigInt("ffffffff", 16)))
  require(round <= 64)
  val constant = new Constant


  private def compress(state: Seq[BigInt]): Seq[BigInt] = {

    var s: Seq[BigInt] = state
    var a = s(0)
    var b = s(1)
    var c = s(2)
    var d = s(3)
    var e = s(4)
    var f = s(5)
    var g = s(6)
    var h = s(7)

    val s0 = _rotr(a, 2) ^ _rotr(a, 13) ^ _rotr(a, 22)
    val maj = (a & b) ^ (a & c) ^ (b & c)
    val t2 = (s0 + maj) & BigInt("ffffffff", 16)
    val s1 = _rotr(e, 6) ^ _rotr(e, 11) ^ _rotr(e, 25)
    val ch = (e & f) ^ ((~e) & g)
    val t1 = (h + s1 + ch + constant.k(round) + messageBlock(round)) & BigInt("ffffffff", 16)
    h = g
    g = f
    f = e
    e = (d + t1) & BigInt("ffffffff", 16)
    d = c
    c = b
    b = a
    a = (t1 + t2) & BigInt("ffffffff", 16)
    s = Seq(a, b, c, d, e, f, g, h)
    s
  }


  private def genFinal(): SHA256CTX = {
    val j: ListBuffer[BigInt] = ListBuffer.fill(8)(0)
    require(round == 63)
    val s = compress(state)

    for (i <- 0 to 7) {
      j(i) = (s(i) + iv(i)) & BigInt("ffffffff", 16)
    }

    new SHA256CTX(j, messageBlock, s, 0)
  }

  def getJ: Seq[BigInt] = {
    val l = iv
    l
  }

  def nextRound: SHA256CTX = {
    if (round < 63) {
      val s = round + 1
      new SHA256CTX(iv, messageBlock, compress(state), s)
    }
    else
      genFinal()
  }
}

object SHA256Model {
  def _rotr(x: BigInt, y: Int): BigInt = {
    ((x >> y) | (x << (32 - y))) & BigInt("ffffffff", 16)
  }


  def generateChunks(message: Seq[BigInt]): Seq[Seq[BigInt]] = {

    //长度
    val s: BigInt = BigInt.int2bigInt(message.length) * 32
    val b: ListBuffer[BigInt] = ListBuffer.fill(2)(0)
    b(0) = s >> 32 & BigInt("ffffffff", 16)
    b(1) = s & BigInt("ffffffff", 16)

    //补位
    val a: ListBuffer[BigInt] = ListBuffer.fill(message.length + 18)(0)
    if (message != null) {
      for (i <- message.indices) {
        a(i) = message(i)
      }
    }
    a(message.length) = BigInt("80000000", 16)
    var padLen = 0
    val r = message.length * 4 & 0x3F
    if (r < 56) {
      padLen = 55 - r
    }
    else {
      padLen = 119 - r
    }

    for (i <- 1 to padLen / 4) {
      a(message.length + i) = BigInt("00000000", 16)
    }
    a(message.length + padLen / 4 + 1) = b(0)
    a(message.length + padLen / 4 + 2) = b(1)
    //切片

    val m: ListBuffer[ListBuffer[BigInt]] = ListBuffer.fill(a.length / 16)(ListBuffer.fill(16)(0))
    for (i <- 0 until a.length / 16) {
      m(i) = a.slice(i * 16, (i + 1) * 16)
    }
    m
  }

  /**
    *
    * use a 16 sized chunk extend whole 64 sized messageBlock
    *
    * @param chunk a 16 sized Seq[BigInt]
    * @return a full 64 sized Seq[BigInt] called messageBlock
    */
  def extend(chunk: Seq[BigInt]): Seq[BigInt] = {
    val m: ListBuffer[BigInt] = ListBuffer.fill(64)(0)
    for (i <- 0 to 15) {
      m(i) = chunk(i)
    }
    for (i <- 16 to 63) {
      val s0: BigInt = _rotr(m(i - 15), 7) ^ _rotr(m(i - 15), 18) ^ (m(i - 15) >> 3) & BigInt("ffffffff", 16)
      val s1: BigInt = _rotr(m(i - 2), 17) ^ _rotr(m(i - 2), 19) ^ (m(i - 2) >> 10) & BigInt("ffffffff", 16)
      m(i) = (m(i - 16) + s0 + m(i - 7) + s1) & BigInt("ffffffff", 16)
    }
    m
  }


  val constant = new Constant

  def apply(iv: Seq[BigInt], messageBlock: Seq[BigInt], state: Seq[BigInt], round: Int): SHA256CTX = new SHA256CTX(iv, messageBlock, state, round)

  def apply(chunk: Seq[BigInt]): SHA256CTX = {
    require(chunk.size == 16)
    new SHA256CTX(
      iv = constant.h,
      messageBlock = extend(chunk),
      state = constant.h,
      round = 0
    )
  }

  def end(end: Seq[BigInt]): String = {

    val a: Seq[BigInt] = end
    val c = generateChunks(a)
    val n: ListBuffer[BigInt] = ListBuffer.fill(8)(0)
    for (i <- 0 to 7) {
      n(i) = constant.h(i)
    }
    for (i <- c.indices) {
      var s = new SHA256CTX(n, extend(c(i)), n, 0)
      for (i <- 1 to 64) {
        s = s.nextRound
      }
      val o: Seq[BigInt] = s.getJ
      for (i <- 0 to 7) {
        n(i) = o(i)
      }
    }
    val k: ListBuffer[String] = ListBuffer.fill(8)("")
    for (i <- 0 to 7) {
      k(i) = String.format("%08x", BigInteger.valueOf(n(i).toLong))
    }
    k(0) + k(1) + k(2) + k(3) + k(4) + k(5) + k(6) + k(7)

  }


  def main(args: Array[String]): Unit = {
    val s = end(Seq.fill(30)("0001dc0d").map(BigInt(_, 16)))
    println(s)
  }
}
