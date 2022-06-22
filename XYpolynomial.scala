

import scala.collection.mutable.ArrayBuffer

//Bivariate polynomials in F_q[x,y]

class XYpolynomial(c:Vector[Vector[FiniteField#FieldElement]]) {
    require(!c.isEmpty)
    val field = c(0)(0).field
    private val zeroF = this.field.zeroElement
    private val oneF = this.field.oneElement
    val q = this.field.q

    private def findXdegree: Int = {
        var degree = c.length-1
        while(degree > 0 && c(degree).forall(_.isZero)){
            degree-=1
        }
        degree
    }
    private def findYdegree: Int = {
        var degree = c(0).length-1
        while( degree > 0 && c.map(_(degree)).forall(_.isZero)){
            degree-=1
        }
        degree
    }

    val xdegree =findXdegree
    val ydegree =findYdegree

    val coefficients = c.map(_.take(ydegree+1)).take(xdegree+1).map(_.map(x => x.asInstanceOf[field.FieldElement]))
    
    def + (p: XYpolynomial): XYpolynomial = {
        val x = scala.math.max(this.xdegree,p.xdegree)
        val y = scala.math.max(this.ydegree,p.ydegree)
        val p1 = this.coefficients.padTo(x+1,Vector.fill[field.FieldElement](y)(zeroF)).map(z => z.padTo(y+1,zeroF))
        val p2 = p.coefficients.padTo(x+1,Vector.fill[field.FieldElement](y)(zeroF)).map(z => z.padTo(y+1,zeroF))
        val newC = p1.zip(p2).map(z => z._1.zip(z._2).map(x => (x._1 + x._2.asInstanceOf[field.FieldElement]) ))
        new XYpolynomial(newC)
    }

    def unary_- : XYpolynomial = {
        new XYpolynomial(coefficients.map(_.map(-_)))
    }

    //Naive polynomial multiplication (better results could be obtained with FFT)
    def * (p: XYpolynomial): XYpolynomial = {
        val x = p.xdegree + this.xdegree
        val y = p.ydegree + this.ydegree
       var newC = Vector.fill[ArrayBuffer[field.FieldElement]](x+1)(ArrayBuffer.fill[field.FieldElement](y+1)(zeroF))
       for(a <- 0 to this.xdegree){
           for(b <- 0 to this.ydegree){
                for(i <- 0 to p.xdegree){
                    for(j <- 0 to p.ydegree){
                        newC(a+i)(b+j) = newC(a+i)(b+j)+(p.coefficients(i)(j).asInstanceOf[field.FieldElement]*this.coefficients(a)(b))
                    }
                }
            }
        }

        new XYpolynomial(newC.map(_.toVector).toVector)
       
    }

    def ^ (exp: Int): XYpolynomial = {
        require(exp>=0)
        var res = new XYpolynomial(Vector(Vector(oneF)))
        var i = 0
        while(i<exp){
            res = res * this
            i+=1
        }
        res
    }

    def scale(a: FiniteField#FieldElement): XYpolynomial = new XYpolynomial(coefficients.map(z => z.map(o => o*a.asInstanceOf[field.FieldElement])))
    def isZero: Boolean = this.coefficients.forall(_.forall(_.isZero))

    //Sort polynomial coefficients with reverse lexicographic ordering with (1,w)-weighted degree
    //Return (coeff,xdegree,ydegree,(xdegree+w*ydegree))
    def sortwLexY(w:Int): Vector[(field.FieldElement,Int,Int,Int)] ={
       
        val sorted = coefficients.map(_.zipWithIndex).zipWithIndex.map(z => z._1.map( f => (f._1, z._2, f._2,z._2+w*f._2))).flatten.sortBy(_._3).sortBy(_._4)
        var count = 0
        while( count < sorted.length-1 && sorted(sorted.length-1-count)._1.isZero){
            count +=1
        }
        sorted.dropRight(count)
    }

    def inputValueY(y:field.FieldElement):XYpolynomial = new XYpolynomial(coefficients.map( _.zipWithIndex.map(z => ( z._1*(y^z._2) ))).map(z => Vector(z.fold(zeroF)(_+_)) ) )
    def inputValueX(x:field.FieldElement):XYpolynomial = new XYpolynomial( coefficients.transpose.map(_.zipWithIndex.map(z => ( z._1 * (x ^ z._2) ))).map(z => Vector(z.fold(zeroF)(_+_))).transpose)
    
    def inputPolY(y:XYpolynomial):XYpolynomial = {
        coefficients.transpose.map(z => new XYpolynomial(Vector(z).transpose)).zipWithIndex.map(z => z._1*(y^z._2)).fold(new XYpolynomial(Vector(Vector(field.zeroElement))))(_+_)
    }

    //Returns polynomial divided with x^r where r is the largest integer s.t. x^r | Q(x,y) (<- this polynomial)
    def divideXpow: XYpolynomial = {
        if(this.isZero){
            return this
        }
        var j = 0
        while(this.coefficients(j).forall(_.isZero)){
            j+=1
        }
            new XYpolynomial(this.coefficients.drop(j))
    }

    //Returns polynomial multiplied with x^p
    def multiplyXpow(p: Int): XYpolynomial = {
        val newC = Vector.fill[Vector[field.FieldElement]](p)(Vector.fill[field.FieldElement](ydegree+1)(zeroF))
        new XYpolynomial(newC ++ this.coefficients)
    }


    //Find y's s.t. Q(0,y)=0
     def findRoots0Y: scala.collection.mutable.ArrayBuffer[field.FieldElement] = {
            val yp = this.inputValueX(field.zeroElement)
            var roots = scala.collection.mutable.ArrayBuffer[field.FieldElement]()
            for(i <- field.elements){
                if(yp.inputValueY(i.asInstanceOf[yp.field.FieldElement]).isZero){
                    roots.append(i)
                }
            }
            roots
        }

    
    //Roth-Ruckenstein Algorithm
    //finds polynomials f(x) s.t Q(x,f(x)) = 0 and deg(f) < degree
    def factor(degree: Int):Vector[XYpolynomial] = {
       
        var out = scala.collection.mutable.ArrayBuffer[XYpolynomial]()
        val g = scala.collection.mutable.ArrayBuffer.fill[field.FieldElement](degree+1)(field.zeroElement)

        def inner(Q:XYpolynomial, lamda:Int): Unit = {
         val T = Q.divideXpow
         for(gamma <- T.findRoots0Y){
            g(lamda)=gamma.asInstanceOf[field.FieldElement]
            if(lamda < degree){
                inner(T.inputPolY(new XYpolynomial(Vector(Vector(gamma,field.zeroElement),Vector(field.zeroElement,field.oneElement)))),lamda+1)
            } else {
                if((Q.inputValueY(g(degree).asInstanceOf[Q.field.FieldElement])).isZero){
                    out.append(new XYpolynomial((Vector(g.toVector).transpose)))
                }
            }
         }
        }
        inner(this,0)
        out.toVector
    }

    override def toString: String = {
        val zipped = coefficients.map(_.zipWithIndex).zipWithIndex.map(z => z._1.map( f => (f._1, f._2+z._2, z._2, f._2))).flatten // (coeff,totalDegree,x,y)
        val sorted = zipped.sortBy(_._2).filterNot(_._1.isZero)
        var string = ""
        if(sorted.forall(_._1.isZero)){
            string = string + "0"
        }
        else{
            for(i <- 0 until sorted.length){
                if( !(sorted(i)._1 == field.oneElement) ) string = string + "(" + sorted(i)._1.toString.dropRight(7 + q.toString.length) + ")"
                if(sorted(i)._1 == field.oneElement && sorted(i)._3 == 0 && sorted(i)._4 == 0) string = string + "(1)"
                if(sorted(i)._3 == 1)  string = string + "X"
                else if(sorted(i)._3 != 0) string = string + "X^" + sorted(i)._3
                if(sorted(i)._4 == 1) string = string + "Y"
                else if(sorted(i)._4 != 0) string = string + "Y^" + sorted(i)._4
                if(i != sorted.length-1)  string = string + " + "
            }
        }
        string + " " + 0x2208.toChar + " GF(" + q + ")[X,Y]"
    }
}
