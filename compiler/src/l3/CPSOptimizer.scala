package l3

import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.TypeTest
import scala.annotation.tailrec

abstract class CPSOptimizer[T <: SymbolicNames]
  (protected val treeModule: T)
  (using TypeTest[treeModule.Atom, treeModule.Literal],
         TypeTest[treeModule.Atom, treeModule.Name],
         TypeTest[treeModule.Tree, treeModule.Body]) {
  import treeModule._
  /** Entry point of abstract class */
  protected def rewrite(tree: Program): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8)(`inline`(_, maxSize)) // use backticks to `inline` method instead of keyword
  }
  /** count
    * 
    * For example, shrinking inlining requires 1 `applied` and 0 `asValue`.
    * 
    * @param applied how many times a function is applied
    * @param asValue how many times a name is used as a value
    */
  private case class Count(applied: Int = 0, asValue: Int = 0)
  /** state
    *
    * @param census  how many times a name is used, for DCE and shrinking inline, is calculated at the start of the shrink phase
    * @param aSubst  record of `Atom` substitutions, for eta reduction, constant folding, common subexpression elimination, absorbing elements, and shrinking inline ?
    * @param cSubst  record of `Cnt`  substitutions, for inlining ?
    * @param eInvEnv for rewriting, e.g., CSE
    *      Pay attention to commutative operations.
    * @param cEnv for continuation inlining
    * @param fEnv for function inlining
    */
  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
    cEnv: Map[Name, Cnt] = Map.empty, // for inlining
    fEnv: Map[Name, Fun] = Map.empty) {
    /** DCE: verify a name is dead */
    def dead(s: Name): Boolean =
      ! census.contains(s)
    /** Shrinking inlining: verify a function/continuation is applied exactly once */
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1))
    /** Determine whether to inline a function/continuation application
      * 
      * We need to verify parameters and arguments match in that the input
      * L₃ programs can be incorrect (see 
      * https://edstem.org/eu/courses/1102/discussion/102705?answer=194371),
      * and they can be wrong during grading
      * (see https://edstem.org/eu/courses/1102/discussion/102705?comment=194427).
      * 
      * @param x function/continuation name
      * @param actualArgs arguments passed to the function/continuation
      *      application
      * @return if a function/continuation is to be inlined AND the number of
      *      parameters and arguments matches
      */
    def hasFun(fun: Name, actualArgs: Seq[Atom]): Boolean =  // to check if inlining is possible
      fEnv.get(fun).exists(_.args.length == actualArgs.length)
    def hasCnt(cnt: Name, actualArgs: Seq[Atom]): Boolean =
      cEnv.get(cnt).exists(_.args.length == actualArgs.length)

    def withASubst(from: Atom, to: Atom): State =  // augment atom substitution
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =  // augment continuation substitution
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
  }

  // Needed for the construction of trees containing other trees,
  // which requires checking (dynamically here) it is indeed a subtype of Body.
  given Conversion[Tree, Body] = {
    case body: Body => body
    case other => sys.error(s"${other} is not a Body")
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  // called recursively
  private def shrink(tree: Tree, s: State): Tree = tree match { // a single pattern match, don't modularize

    case LetF(funs: Seq[Fun], body: Tree) => 
      var s_ = s
      val funs_ = funs.filter ( f =>
        if (s_.dead(f.name)) // DCE
          false
        else f.body match { // eta reduction
          case AppF(n: Name, f.retC, f.args) => // pattern match on value ???
            s_ = s_.withASubst(f.name, s_.aSubst.getOrElse(n, n))
            false
          case _ => true
        }
      )

      val funs__ = funs_ map (f =>  // shrink the body of the function
        Fun(f.name, f.retC, f.args, shrink(f.body, s_))
      )
      LetF(funs__, shrink(body, s_))

    case LetC(cnts: Seq[Cnt], body: Tree) =>
      var s_ = s_
      val cnts_ = cnts.filter(c =>
        if (s_.dead(c.name)) // DCE
          false
        else c.body match { // eta reduction
          case AppC(n: Name, c.args) => // pattern match on value ???
            s_ = s_.withCSubst(c.name, s_.cSubst.getOrElse(n, n))
            false
          case _ => true
        }
      )

      val cnts__ = cnts_ map (c =>  // shrink the body of the continuation
        Cnt(c.name, c.args, shrink(c.body, s_))
      )
      LetC(cnts__, shrink(body, s_))


  

    case LetP(name: Name, prim: ValuePrimitive, args: Seq[Atom], body: Tree) =>
      if s.dead(name) // DCE
        shrink(body, s)
      else if vEvaluator.isDefinedAt((prim, args))
        shrink(body, s.withASubst(name, vEvaluator((prim, args))))
      else if leftNeutral.contains((args(0), prim)) || rightNeutral.contains((prim, args(1)))
        ???
      else if !(impure(prim) || unstable(prim)) && s.eInvEnv.contains((prim, args)) // CSE
        shrink(body, s.withASubst(name, s.eInvEnv((prim, args))))
      else if commutative(prim) // commutative operations: +, *, &, |, and ^
        LetP(name, prim, args map s.aSubst, shrink(body, s.withExp(name, prim, args).withExp(name, prim, args.reverse)))
      else if !(impure(prim) || unstable(prim)) // non-commutative and unary operations without side effects
        LetP(name, prim, args map s.aSubst, shrink(body, s.withExp(name, prim, args)))
      else // impure or unstable operations
        LetP(name, prim, args map s.aSubst, shrink(body, s))

  }

  // (Non-shrinking) inlining
  // need to duplicate(rename) names bound in the inlined function

  private def inline(tree: Tree, maxSize: Int): Tree = {
    /** Copy a tree */
    def copyT(t: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = t match {
      case LetF(funs, body) =>
        val names = funs map (_.name)
        val names1 = names map (_.copy())
        val subV1 = subV ++ (names zip names1)
        LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
      case LetC(cnts, body) =>
        val names = cnts map (_.name)
        val names1 = names map (_.copy())
        val subC1 = subC ++ (names zip names1)
        LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
      case LetP(name, prim, args, body) =>
        val name1 = name.copy()
        LetP(name1, prim, args map subV,
          copyT(body, subV + (name -> name1), subC))
      case AppF(fun, retC, args) =>
        AppF(subV(fun), subC(retC), args map subV)
      case AppC(cnt, args) =>
        AppC(subC(cnt), args map subV)
      case If(cond, args, thenC, elseC) =>
        If(cond, args map subV, subC(thenC), subC(elseC))
      case Halt(arg) =>
        Halt(subV(arg))
    }
    /** Copy a function */
    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ (fun.args zip args1)
      val funName1 = subV(fun.name).asInstanceOf[Name]
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }
    /** Copy a continuation */
    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ (cnt.args zip args1)
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(using s: State): Tree = // create a stream of trees, the nth tree is the result of inlining functions of size <= fibonacci(n)
        tree match {
          case LetC(cnts: Seq[Cnt], body: Body) => {
            val _cnts = cnts.filter((cnt: Cnt) => size(cnt.body) <= cntLimit)
            inlineT(body)(using s.withCnts(_cnts))
          }
          case AppC(cnt: Name, args: Seq[Atom]) => {
            if (s.hasCnt(cnt, args))
              s.cEnv(cnt) match
                case Cnt(c, as, e) =>
                  copyT(e, subst(as, args), emptySubst[Name])
            else   // Even though an inner `AppC` must correpsond to an outer
              tree // `LetC`, `cEnv` may still not contain `cnt` due to size
          }        // limit.
          case LetF(funs: Seq[Fun], body: Body) => {
            val _funs = funs.filter((fun: Fun) => size(fun.body) <= funLimit)
            inlineT(body)(using s.withFuns(_funs))
          }
          case AppF(fun: Atom, retC: Name, args: Seq[Atom]) => {
            if (s.hasFun(fun.asInstanceOf[Name], args))
              s.fEnv(fun.asInstanceOf[Name]) match
                case Fun(f, c, as, e) =>
                  copyT(e, subst(as, args), subst(c, retC))
            else   // Even though an inner `AppF` must correpsond to an outer
              tree // `LetF`, `fEnv` may still not contain `fun` due to size
          }        // limit.
          case LetP(name, prim, args, body) =>
            LetP(name, prim, args, inlineT(body))
          // `If` and `Halt`
          case t: Tree => t
        }

      (i + 1, fixedPoint(inlineT(tree)(using State(census(tree))))(shrink))
    }

    trees.takeWhile{ (_, tree) => size(tree) <= maxSize }.last._2  // take the last tree that fits in maxSize
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(applied = currCount.applied + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    def incValUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(asValue = currCount.asValue + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    @tailrec
    def addToCensus(tree: Tree): Unit = tree match {
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = tree match {
    case LetF(fs, body) => fs.map(_.body).map(size).sum + size(body)
    case LetC(cs, body) => cs.map(_.body).map(size).sum + size(body)
    case LetP(_, _, _, body) => size(body) + 1
    case _: (AppF | AppC | If | Halt) => 1
  }

  // up until this point, the code is common to both optimizers
  // 
  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAlloc: ValuePrimitive
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] 
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean]
  protected val commutative: ValuePrimitive => Boolean
}

object HighCPSOptimizer extends CPSOptimizer(HighCPSTreeModule)
    with (HighCPSTreeModule.Program => HighCPSTreeModule.Program) {
  import treeModule._
  import CL3Literal._, L3Primitive._

  def apply(program: Program): Program =
    rewrite(program)

  private[this] given Conversion[L3Int, Literal] = IntLit.apply
  private[this] given Conversion[Int, Literal] = L3Int.apply

  // TODO: check `FlatCPSOptimizer` for populating values below
  protected val impure: ValuePrimitive => Boolean =
    Set(ByteRead, ByteWrite, BlockSet)

  protected val unstable: ValuePrimitive => Boolean =
    Set(BlockAlloc, BlockGet, ByteRead)

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), IntAdd), (IntLit(1), IntMul), (IntLit(~0), IntBitwiseAnd), (IntLit(0), IntBitwiseOr), (IntLit(0), IntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((IntAdd, IntLit(0)), (IntSub, IntLit(0)), (IntMul, IntLit(1)), (IntDiv, IntLit(1)),
        (IntShiftLeft, IntLit(0)), (IntShiftRight, IntLit(0)),
        (IntBitwiseAnd, IntLit(~0)), (IntBitwiseOr, IntLit(0)), (IntBitwiseXOr, IntLit(0)))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), IntMul), (IntLit(0), IntDiv),
        (IntLit(0), IntShiftLeft), (IntLit(0), IntShiftRight),
        (IntLit(0), IntBitwiseAnd), (IntLit(~0), IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, IntLit(0)), (IntAnd, IntLit(0)), (IntBitwiseOr, IntLit(~0)))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => IntLit(0)
    case (IntDiv, _) => IntLit(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case IntLe | Eq => BooleanLit(true)
    case IntLt => BooleanLit(false)
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal] = {
    case (IntAdd, Seq(x: Literal, y: Literal)) => IntLit(x.value + y.value)
    case (IntSub, Seq(x: Literal, y: Literal)) => IntLit(x.value - y.value)
    case (IntMul, Seq(x: Literal, y: Literal)) => IntLit(x.value * y.value)
    case (IntDiv, Seq(x: Literal, y: Literal)) if y.value.toInt != 0 => IntLit(x.value / y.value)
    case (IntMod, Seq(x: Literal, y: Literal)) if y.value.toInt != 0 => IntLit(x.value % y.value)

    case (IntShiftLeft , Seq(x: Literal, y: Literal)) => IntLit(x.value << y.value)
    case (IntShiftRight, Seq(x: Literal, y: Literal)) => IntLit(x.value >> y.value)
    case (IntBitwiseAnd, Seq(x: Literal, y: Literal)) => IntLit(x.value  & y.value)
    case (IntBitwiseOr , Seq(x: Literal, y: Literal)) => IntLit(x.value  | y.value)
    case (IntBitwiseXOr, Seq(x: Literal, y: Literal)) => IntLit(x.value  ^ y.value)
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean] = {
    case (IntLt, Seq(x: Literal, y: Literal)) => x.value <  y.value
    case (IntLe, Seq(x: Literal, y: Literal)) => x.value <= y.value
    case (Eq   , Seq(x: Literal, y: Literal)) => x.value == y.value
  }

  protected val commutative: ValuePrimitive => Boolean = 
    Set(IntAdd, IntMul, IntBitwiseAnd, IntBitwiseOr, IntBitwiseXOr)
}

object FlatCPSOptimizer extends CPSOptimizer(FlatCPSTreeModule)
    with (FlatCPSTreeModule.Program => FlatCPSTreeModule.Program) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(program: Program): Program = rewrite(program) match {
    case tree: Program => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean =
    Set(BlockAlloc, BlockGet, ByteRead) // why `BlockGet`?

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
        (ShiftLeft, 0), (ShiftRight, 0),
        (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
        (0, ShiftLeft), (0, ShiftRight),
        (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => 0
    case (Div, _) => 1
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
                                            Literal] = {
    case (Add, Seq(x: Literal, y: Literal)) => x + y
    case (Sub, Seq(x: Literal, y: Literal)) => x - y
    case (Mul, Seq(x: Literal, y: Literal)) => x * y
    case (Div, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x / y
    case (Mod, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x: Literal, y: Literal)) => x << y
    case (ShiftRight, Seq(x: Literal, y: Literal)) => x >> y
    case (And, Seq(x: Literal, y: Literal)) => x & y
    case (Or,  Seq(x: Literal, y: Literal)) => x | y
    case (XOr, Seq(x: Literal, y: Literal)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
                                            Boolean] = {
    case (Lt, Seq(x: Literal, y: Literal)) => x < y
    case (Le, Seq(x: Literal, y: Literal)) => x <= y
    case (Eq, Seq(x: Literal, y: Literal)) => x == y
  }

  protected val commutative: ValuePrimitive => Boolean =
    = Set(Add, Mul, And, Or, XOr)
}
