import scala.util.Random

//Helper object for creating finite fields
object GF {
    
    def apply(q: Int): FiniteField = {
        require(Primer.isPrimePower(q))
        if(Primer.isPrime(q)) new PrimeField(q)
        else new PrimePowerField(q)
  
    }
}

abstract class FiniteField(size: Int) {
    //counts the number of operations performed in the field (+,*,-,^(-1))
    var operationCount: BigInt = 0

    val q = size
    val elements: Vector[FieldElement] = (0 to q-1).toVector.map(x => new FieldElement(x))
    val ringElements: Vector[RingElement]
    val primitiveElement: RingElement

    def findPrimitiveElement: (RingElement, Vector[RingElement])
    def setCountZero = operationCount=0
    def zeroElement = elements(0)
    def oneElement = elements(1)

    //Precomputed field operations:
    val sums: Vector[Vector[Int]]
    val minus : Vector[Int]
    val mult: Vector[Vector[Int]] = Vector.fill[Vector[Int]](q)((0 to q-1).toVector).zipWithIndex
    .map(x => x._1.map(z => if(z == 0 || x._2==0){0} else  ((z + x._2-2) % (q-1)) + 1))
    val multinv: Vector[Int] = (0 until q).toVector.map(x => (((q-2)*(x-1))%(q-1))+1)

    //Field element's primitive power + 1 to corresponding ring element
    def pPPOtoRE(pPPO: Int): RingElement

    class FieldElement(exp: Int) {

        //Primitive power plus 1 (additive identity = 0, multiplicative identity = 1, ..., q)
        def pPPO = exp
        def field = FiniteField.this
        def q = field.q
        def + (e: FieldElement): FieldElement = {
            operationCount += 1
            elements(sums.apply(e.pPPO).apply(exp))}
        def unary_- : FieldElement = {
            operationCount += 1
            elements(minus(exp))}
        def * (e: FieldElement): FieldElement = {
             operationCount += 1
            elements(mult(e.pPPO)(exp))}
        def ^ (exp: Int ): FieldElement = {
            var j = 0
            var res = elements(1)
            while(j<exp){
                res = res*this
                j+=1
            }
            res
        }
        def inv: FieldElement = {
            operationCount += 1
            require(!this.isZero)
            elements(multinv(exp))
        }
        def == (e: FieldElement): Boolean = exp == e.pPPO
        def isZero: Boolean = exp == 0
        def toRingElement: RingElement = field.pPPOtoRE(exp)
        override def toString: String = {
            var string = ""
            if(this.isZero){string = "0"} else{ string = 0x03B3.toChar + "^" + (exp-1)}
            string + " "+ 0x2208.toChar +" GF(" + this.q + ")" 
        } 
    }
    
    def randElement: FieldElement = elements(Random.nextInt(q))

    override def toString: String = "GF(" + q + ")"
}



class PrimePowerField(size: Int) extends FiniteField(size) {
    require(Primer.isPrimePower(size))
    val prime = Primer.findPrimePower(q)._1
    val power = Primer.findPrimePower(q)._2
   
    private def findIrreducible: Polynomial = {
        var i = new Polynomial(Vector(new Residue(0,prime)))
        while(!i.isIrreducible || i.isZero) {
            i = new Polynomial(( Vector.fill[Int](power)(Random.nextInt(prime)) :+ (Random.nextInt(prime-1)+1) ).map( x => new Residue(x,prime)))
        } 
        i
    }
    private def combinator: Vector[Vector[Int]] = {
        val list = List.fill[List[Int]](power)((0 until prime).toList)
        def inner(list: List[List[Int]]): List[List[Int]] = {
            list match {
                case Nil    => List(Nil)
                case h :: _ => h.flatMap(i => inner(list.tail).map(_ :+ i))
            }
        }
        inner(list).map(_.toVector).toVector
    }
    val irp = findIrreducible

    val ringElements: Vector[Polynomial] = combinator.map(z => new Polynomial(z.map(x => new Residue(x,prime))) )

    def findPrimitiveElement: (Polynomial, Vector[Polynomial]) = { 
         if(q == 2) return (ringElements(1),Vector(ringElements(1)))
        var count = 2
        while(count < ringElements.length){
            val e = ringElements(count)
            var p = ringElements(1)
            var powers = scala.collection.mutable.ArrayBuffer[Polynomial]()
            
            while( (!(p == e) || powers.length < 2) && powers.length < (q-1)){
                powers = powers.append(p)
                p = e*p % irp
            }
            if(powers.length == (q-1)) return (powers(1),powers.toVector)
            count += 1
        }
        (ringElements(0),Vector())
    }

    

    val (primitiveElement, primitivePowers) = this.findPrimitiveElement

     //Index of ring elements is their primitive power + 1
    val primitivePowersPlusOne = new Polynomial(Vector(new Residue(0,prime))) +: primitivePowers

    //Map from polynomial coefficients to corresponding primitive powers
    val polCofToPPPO = primitivePowersPlusOne.map(_.coeff.map(_.value)).zipWithIndex.toMap
   
    val sums: Vector[Vector[Int]] = primitivePowersPlusOne.map(Vector.fill[Polynomial](q)(_)).map( x => (x.zip(primitivePowersPlusOne).map(x => polCofToPPPO(( (x._1 + x._2) % irp ).coeff.map(_.value)) )))
    val minus : Vector[Int] = primitivePowersPlusOne.map(x => polCofToPPPO((-x).coeff.map(_.value)))

    def pPPOtoRE(pPPO: Int): RingElement = if(pPPO == 0){ringElements(0)} else primitiveElement.powmod(pPPO-1,irp)
}


class PrimeField(size: Int) extends FiniteField(size) {
    require(Primer.isPrime(size))

    val ringElements: Vector[Residue] = (0 until q).toVector.map(x => new Residue(x,q))

    def findPrimitiveElement: (Residue, Vector[Residue]) = { 
         if(q == 2) return (ringElements(1),Vector(ringElements(1)))
        var count = 2
        while(count < ringElements.length){
            val e = ringElements(count)
            var p = ringElements(1)
            var powers = scala.collection.mutable.ArrayBuffer[Residue]()
            
            while( (!(p == e) || powers.length < 2) && powers.length < (q-1)){
                powers = powers.append(p)
                p = e*p
            }
            if(powers.length == (q-1)) return (powers(1),powers.toVector)
            count += 1
        }
        (ringElements(0),Vector())
    }
    
    
    val (primitiveElement, primitivePowers) = this.findPrimitiveElement

    //Index of ring element is their primitive power + 1
    val primitivePowersPlusOne = new Residue(0,q) +: primitivePowers

    //residue values to primitive powers + 1
    val resToPPPO = primitivePowersPlusOne.map(_.value).zipWithIndex.toMap
    val sums = primitivePowersPlusOne.map(Vector.fill[Residue](q)(_)).map( x => (x.zip(primitivePowersPlusOne).map(x => resToPPPO((x._1 +x._2).value) )))
    val minus = primitivePowersPlusOne.map(x => resToPPPO((-x).value))

    def pPPOtoRE(pPPO: Int): RingElement = if(pPPO == 0){ringElements(0)} else primitiveElement^(pPPO-1)
   
    
}
