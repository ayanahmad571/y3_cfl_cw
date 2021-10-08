/* 
 * Author: Ayan Ahmad
*/

abstract class Rexp
case object ZERO extends Rexp                                // matches nothing
case object ONE extends Rexp                                 // matches an empty string
// case class CHAR(c: Char) extends Rexp                        // matches a character c
case class ALT(r1: Rexp, r2: Rexp) extends Rexp              // alternative
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp              // sequence
case class STAR(r: Rexp) extends Rexp                        // star

/*______ Extended Cases - Classes ______*/
// case class RANGE(s: Set[Char]) extends Rexp                  // range, gives a set of characters
case class PLUS(r: Rexp) extends Rexp                        // plus, 1 or more of r
case class OPTIONAL(r: Rexp) extends Rexp                    // optional 
case class NTIMES(r: Rexp, n: Int) extends Rexp              // n times
case class UPTO(r: Rexp, m: Int) extends Rexp                // up until
case class FROM(r: Rexp, n: Int) extends Rexp                // from
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp     // between n and m but more than 0 
case class NOT(r: Rexp) extends Rexp                         // not r
case class CFUN(f: Char => Boolean) extends Rexp             // single construction, 


// CFUN translations
def CHAR(c : Char) = CFUN((ch : Char) => c == ch)
def RANGE(s: Set[Char]) = CFUN((ch : Char) => s.contains(ch))
def ALL = CFUN ((_ : Char) => true)


// nullable function: tests whether a regular expression can recognise the empty string
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
	//   case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  
  /*______ Extended Cases ______*/
	//   case RANGE(s) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case UPTO(r, _) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, _) => if (n == 0) true else nullable(r) 
  case NOT(r) => !nullable(r)
  case CFUN(_) => false
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
	case ZERO => ZERO
	case ONE => ZERO
	// case CHAR(d) => if (c == d) ONE else ZERO
	case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
	case SEQ(r1, r2) => if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2)) else SEQ(der(c, r1), r2)
	case STAR(r1) => SEQ(der(c, r1), STAR(r1))

	/*______ Extended Cases ______*/
	// case RANGE(s) => if (s.contains(c)) ONE else ZERO
	case PLUS(r) => SEQ(der(c, r), STAR(r))
	case OPTIONAL(r) => der(c, r)
	case NTIMES(r, n) => if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
	case UPTO(r, m) => if (m <= 0) ZERO else SEQ(der(c, r), UPTO(r, m - 1)) // less than = is used for capping Between's 0 case
	case FROM(r, n) => if (n == 0) SEQ(der(c, r), FROM(r, n)) else SEQ(der(c, r), FROM(r, n - 1))
	case BETWEEN(r, n, m) => if (n == 0) SEQ(der(c, r), UPTO(r, m - 1 )) else SEQ(der(c, r), BETWEEN(r, n - 1, m - 1)) // if n = 0, then it is same as upto
	case NOT(r) => NOT(der(c, r))
	case CFUN(f) => if(f(c)) ONE else ZERO
}

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}


// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))


//Question 5
val myEmail = "ayan.ahmad@kcl.ac.ukssssaaaaaa"


// Email Breakup
//  abc@gmail.com
//  username@domain.tld

// https://stackoverflow.com/questions/8556255/how-do-i-create-a-set-of-characters-in-scala
val alphabets = ('a' to 'z').toSet;
val numbers = ('0' to '9').toSet;

val username = PLUS(RANGE(alphabets ++ numbers + '_' + '.' + '-'))
val domain = PLUS(RANGE(alphabets ++ numbers + '.' + '-'))
val tld = BETWEEN(RANGE(alphabets + '.'),2,6)

val email_regex = SEQ(username, SEQ(CHAR('@'), SEQ(domain, SEQ(CHAR('.'), tld))))

matcher(email_regex, myEmail)

