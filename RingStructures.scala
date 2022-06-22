
import scala.util.Random

//Helper object for prime related functions 

object Primer {
    def isPrime(number: Int): Boolean = {
        if (number < 4) number > 1
        else if (number % 2 == 0 || number % 3 == 0) false
        else (5 to math.sqrt(number).toInt by 6).forall(i => number % i != 0 && number % (i + 2) != 0)
    }

    def isPrimePower(number: Int): Boolean = {
        if(isPrime(number)) true
        else {
            val primes = (2 to math.sqrt(number).toInt).filter(isPrime(_))
            for(p <- primes){
                var div = number
                while(div % p == 0){
                    div = div / p
                    if(div == 1) return true
                }
            }
            false 
        }
    }

    def findPrimePower(number: Int): (Int,Int) = {
        require(isPrimePower(number))
        val primes = (2 to math.sqrt(number).toInt).filter(isPrime(_))
        for(p <- primes){
            var div = number
            var count = 1
            while(div % p == 0){
                div = div / p
                if(div == 1) return (p, count)
                count += 1
            }
        }
        (0,0)
    }
}

abstract class RingElement {   
    type E <: RingElement
    def + (e: E): E
    def unary_- : E
    def * (e: E): E
    def ^ (e: Int ): E
    def == (e: E): Boolean
    def isZero: Boolean
}




//Elementents of Z_p ring

class Residue(a: Int, size:Int) extends RingElement {
    type E = Residue
    val q = size
    val value = a % q
    def + (r: Residue): Residue = new Residue((this.value + r.value) % q, q)
    def unary_- : Residue = new Residue(q - value,q)
    def * (r: Residue): Residue = new Residue( (this.value * r.value) % q, q)
    def ^ (exp: Int): Residue = {
        var res = 1
        for(i <- 0 until exp){
            res = (res * this.value) % q
        }
        new Residue(res, q)
    }
    //inverse exists only if q is prime
    def inv: Residue = {
    require(this.value != 0)
     this^(q-2) 
    }
    override def toString: String = value.toString
    def isZero = this.value == 0
    def == (e: Residue) = this.value == e.value
}

//Polynomials over Ring Z_p 
class Polynomial(p: Vector[Residue]) extends RingElement {
    type E = Polynomial
    val q = p(0).q
    private val zero = new Residue(0,q)
    private val one = new Residue(1,q)
    private def findDegree: Int = {
        var res = p.length-1
        while(res > 0 && p(res).value == 0){
            res-=1
        }
        res
    }
    val degree = findDegree
    
    val coeff = p.take(degree+1)
  
    def isZero: Boolean = coeff(0).value == 0 && degree == 0
    
    def + (a: Polynomial): Polynomial = {
        new Polynomial( this.coeff.padTo(math.max(this.degree,a.degree)+1,zero)
        .zip(a.coeff.padTo(math.max(this.degree,a.degree)+1,zero)).map(x => x._1 + x._2))
    }
    def unary_- : Polynomial = new Polynomial( this.coeff.map(-_))

    def == (a: Polynomial): Boolean = if(this.coeff.length != a.coeff.length){return false} else this.coeff.zip(a.coeff).forall(x => x._1 == x._2)

    def * (a: Polynomial): Polynomial = {
        var result = new Polynomial(Vector(zero))
        for((c, exp) <- coeff.zipWithIndex) {
            val newc = new scala.collection.mutable.ArrayBuffer[Residue]()
            for(i <- 0 until exp) newc.append(zero)
            for(c2 <- a.coeff) newc.append(c*c2)
            result = result + new Polynomial(newc.toVector)
        }
        result
    }

    def ^ (exp: Int): Polynomial = {
        require(exp >= 0)
        Vector.fill[Polynomial](exp)(this).fold(new Polynomial(Vector(one)))(_*_)    
    }

    def / (a: Polynomial): (Polynomial,Polynomial) = {
        require(!a.isZero)
        var quotient = new Polynomial(Vector(zero))
        var remainder = this
        val divasorLC = a.coeff.last
        val divasorDeg = a.degree
        while(remainder.degree >= divasorDeg && !remainder.isZero) {
            val divV = Vector.fill(remainder.degree - divasorDeg+1)(zero).updated(remainder.degree - divasorDeg, remainder.coeff.last * divasorLC.inv)
            val divP = new Polynomial(divV)
            remainder = remainder+(-(divP * a))
            quotient = quotient + divP
        }
        (quotient, remainder)
    }

    def % (a: Polynomial): Polynomial = (this / a)._2

    def gcd (a: Polynomial): Polynomial = {
        var dividend = this
        var divider = a
        if(divider.degree > dividend.degree) {
            divider.gcd(dividend)
        } 
        else {
            while(!divider.isZero) {
                val (q,r) = dividend / divider
                dividend = divider
                divider = r
            } 
            dividend
        }
    }

    def powmod (exp: Int, pol: Polynomial): Polynomial = {
        require(exp >= 0)
        Vector.fill[Polynomial](exp)(this).fold(new Polynomial(Vector(one)))( (a,b) => (a * b) % pol)    
    }

    def isIrreducible: Boolean = {
        val x = new Polynomial(Vector(zero,one))
        var pow = x
        for(i <- 0 until this.degree / 2){
            pow =  pow.powmod(q,this) 
            val thisGCD = this.gcd(pow+(-x))
            if(!(thisGCD.degree == 0)){
                return false
            }
        }
        true
    }

    override def toString: String = {
        var string = ""
        if(coeff.forall(_.value == 0)) string = "0 "
        else{
            for(i <- 0 until coeff.length){
                if(i == 0 && coeff(i).value != 0){
                    string = string + coeff(i) + " "
                }
                else if(coeff(i).value >= 2 && i == 1) string = string + coeff(i) + 0x03B1.toChar + " "
                else if(coeff(i).value == 1 && i == 1) string = string + 0x03B1.toChar + " "
                else if( coeff(i).value >= 2) string = string + coeff(i) + 0x03B1.toChar + "^" + i + " "
                else if(coeff(i).value == 1) string = string + 0x03B1.toChar + "^" + i + " "
                if(i != coeff.length-1 && coeff(i).value != 0) string = string + "+ "
            }
        }
        string + 0x2208.toChar + " " + 0x2124.toChar + "_" + q + "[" + 0x03B1.toChar + "]"
    }
    
}










