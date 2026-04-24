package side.effect.free

import soot.jimple.*
import soot.jimple.spark.pag.PAG
import soot.jimple.toolkits.callgraph.{CallGraph, ContextSensitiveCallGraph, ReachableMethods}
import soot.jimple.toolkits.pointer.SideEffectAnalysis
import soot.options.Options
import soot.tagkit.*
import soot.toolkits.exceptions.ThrowAnalysis
import soot.util.*
import soot.{Unit => SootUnit, *}

import java.io.File
import java.nio.file.Path
import scala.jdk.CollectionConverters.*
import scala.util.Try

object Wrappers {

  private def ifToOption[T](condition: => Boolean, positiveResult: => T): Option[T] =
    if (condition) Some(positiveResult) else None

  // ── Numberable ──────────────────────────────────────────────────────────────

  extension (n: Numberable) {
    def number: Int                    = n.getNumber
    def number_=(newNumber: Int): Unit = n.setNumber(newNumber)
  }

  // ── SootClass ───────────────────────────────────────────────────────────────

  object SSootClass {
    def apply(
        name: String,
        modifiers: Int = Modifier.PUBLIC,
        fields: Iterable[SootField] = Iterable(),
        interfaces: Iterable[SootClass] = Iterable(),
        superClass: Option[SootClass] = None,
        methods: Iterable[SootMethod] = Iterable(),
        outerClass: Option[SootClass] = None,
        annotations: Iterable[AnnotationTag] = Iterable()
    ): SootClass = {
      val sc = new SootClass(name, modifiers)
      superClass.foreach(sc.setSuperclass)
      outerClass.foreach(sc.setOuterClass)
      fields.foreach(sc.addField)
      interfaces.foreach(sc.addInterface)
      methods.foreach(sc.addMethod)
      if (annotations.nonEmpty) sc.addTag(SVisibilityAnnotationTag(annotations))
      sc
    }
  }

  extension (v: SootClass) {
    def name: String                    = v.getName
    def name_=(n: String): Unit         = v.setName(n)
    def packageName: String             = v.getPackageName
    def shortName: String               = v.getShortName
    def modifiers: Int                  = v.getModifiers
    def modifiers_=(m: Int): Unit       = v.setModifiers(m)
    def fields: Chain[SootField]        = v.getFields
    def fields_+=(f: SootField): Unit   = v.addField(f)
    def interfaces: Chain[SootClass]    = v.getInterfaces
    def interfaces_=(is: Iterable[SootClass]): Unit = {
      v.getInterfaces.iterator().asScala.foreach(v.removeInterface)
      is.foreach(v.addInterface)
    }
    def interfaces_+=(i: SootClass): Unit         = v.addInterface(i)
    def superclass: SootClass                     = v.getSuperclass
    def superclass_=(sc: SootClass): Unit         = v.setSuperclass(sc)
    def superClassOpt: Option[SootClass]          = ifToOption(v.hasSuperclass, v.getSuperclass)
    def methods: Iterable[SootMethod]             = v.getMethods.asScala
    def methods_+=(m: SootMethod): Unit           = v.addMethod(m)
    def outerClass: SootClass                     = v.getOuterClass
    def outerClass_=(sc: SootClass): Unit         = v.setOuterClass(sc)
    def outerClassOpt: Option[SootClass]          = ifToOption(v.hasOuterClass, v.getOuterClass)
    def typ: RefType                              = v.getType
    def typ_=(t: RefType): Unit                   = v.setRefType(t)
    def field(subSig: String): SootField          = v.getField(subSig)
    def fieldOpt(subSig: String): Option[SootField]           = Option(v.getFieldUnsafe(subSig))
    def field(name: String, typ: Type): SootField             = v.getField(name, typ)
    def fieldOpt(name: String, typ: Type): Option[SootField]  = Option(v.getFieldUnsafe(name, typ))
    def fieldByName(name: String): SootField                  = v.getFieldByName(name)
    def fieldByNameOpt(name: String): Option[SootField]       = Option(v.getFieldByNameUnsafe(name))
    def fieldsByName(name: String): Iterable[SootField]       = v.getFields.asScala.filter(_.getName == name)
    def methodsByName(name: String): Iterable[SootMethod]     = v.getMethods.asScala.filter(_.getName == name)
    def methodByName(name: String): SootMethod                = v.getMethodByName(name)
    def methodByNameOpt(name: String): Option[SootMethod]     = Option(v.getMethodByNameUnsafe(name))
    def method(subSig: String): SootMethod                    = v.getMethod(subSig)
    def methodOpt(subSig: String): Option[SootMethod]         = Option(v.getMethodUnsafe(subSig))
    def method(subSig: NumberedString): SootMethod            = v.getMethod(subSig)
    def methodOpt(subSig: NumberedString): Option[SootMethod] = Option(v.getMethodUnsafe(subSig))
    def method(name: String, paramTypes: List[Type]): SootMethod = v.getMethod(name, paramTypes.asJava)
    def methodOpt(name: String, paramTypes: Seq[Type]): Option[SootMethod] = {
      val p = paramTypes.asJava
      ifToOption(v.declaresMethod(name, p), v.getMethod(name, p))
    }
    def method(name: String, paramTypes: List[Type], retType: Type): SootMethod =
      v.getMethod(name, paramTypes.asJava, retType)
    def methodOpt(name: String, paramTypes: List[Type], retType: Type): Option[SootMethod] =
      Option(v.getMethodUnsafe(name, paramTypes.asJava, retType))
    def inScene_=(flag: Boolean): Unit       = v.setInScene(flag)
    def resolvingLevel_=(lvl: Int): Unit     = v.setResolvingLevel(lvl)
  }

  // ── CallGraph ───────────────────────────────────────────────────────────────

  extension (v: CallGraph) {
    def callersOf(callee: SootMethod)   = v.edgesInto(callee).asScala.map(_.getSrc.method())
    def calleesOf(callSite: SootUnit)   = v.edgesOutOf(callSite).asScala.map(_.getTgt.method())
    def calleesFrom(method: SootMethod) = v.edgesOutOf(method).asScala.map(_.getTgt.method())
  }

  // ── RefType ─────────────────────────────────────────────────────────────────

  extension (v: RefType) {
    def anySubType: AnySubType              = v.getAnySubType
    def anySubType_=(ast: AnySubType): Unit = v.setAnySubType(ast)
    def arrayElementType: Type              = v.getArrayElementType
    def arrayType: ArrayType                = v.getArrayType
    def arrayType_=(at: ArrayType): Unit    = v.setArrayType(at)
    def className: String                   = v.getClassName
    def className_=(cn: String): Unit       = v.setClassName(cn)
    def sootClass: SootClass                = v.getSootClass
    def sootClass_=(sc: SootClass): Unit    = v.setSootClass(sc)
  }

  // ── ClassMember ─────────────────────────────────────────────────────────────

  extension (c: ClassMember) {
    def declaringClass: SootClass       = c.getDeclaringClass
    def modifiers: Int                  = c.getModifiers
    def modifiers_=(m: Int): Unit       = c.setModifiers(m)
    def phantom_=(flag: Boolean): Unit  = c.setPhantom(flag)
  }

  // ── SootField ───────────────────────────────────────────────────────────────

  extension (v: SootField) {
    def name: String           = v.getName
    def name_=(n: String): Unit = v.setName(n)
    def signature: String      = v.getSignature
    def subSignature: String   = v.getSubSignature
    def declaration: String    = v.getDeclaration
    def quasiSignature: String = v.getDeclaringClass.getName + "." + v.getName
    def typ: Type              = v.getType
  }

  // ── SootMethod ──────────────────────────────────────────────────────────────

  extension (v: SootMethod) {
    def isClinit: Boolean                    = v.getName == "<clinit>"
    def name: String                         = v.getName
    def name_=(n: String): Unit              = v.setName(n)
    def declared: Boolean                    = v.isDeclared
    def declared_=(flag: Boolean): Unit      = v.setDeclared(true)
    def signature: String                    = v.getSignature
    def subSignature: String                 = v.getSubSignature
    def body: Body                           = v.retrieveActiveBody()
    def body_=(b: Body): Unit                = v.setActiveBody(b)
    def bodyOpt: Option[Body]                = ifToOption(v.hasActiveBody, v.getActiveBody)
    def source: MethodSource                 = v.getSource
    def source_=(ms: MethodSource): Unit     = v.setSource(ms)
    def parameterCount: Int                  = v.getParameterCount
    def parameterTypes: Iterable[Type]       = v.getParameterTypes.asScala
    def parameterTypes_=(pt: Seq[Type]): Unit = v.setParameterTypes(pt.asJava)
    def exceptions: Iterable[SootClass]      = v.getExceptions.asScala
    def exceptions_=(ex: Seq[SootClass]): Unit = v.setExceptions(ex.asJava)
    def returnType: Type                     = v.getReturnType
    def returnType_=(t: Type): Unit          = v.setReturnType(t)
    def declaringClass: SootClass            = v.getDeclaringClass
    def declaringClass_=(sc: SootClass): Unit = { v.setDeclaringClass(sc); v.setDeclared(true) }
    def locals: Chain[Local]                 = if (v.hasActiveBody) v.body.getLocals else new HashChain[Local]()
    def units: Chain[SootUnit]               = if (v.hasActiveBody) v.body.getUnits else new HashChain[SootUnit]()
    def statements: Chain[Stmt]              = if (v.hasActiveBody) v.body.getUnits.asInstanceOf[Chain[Stmt]] else new HashChain[Stmt]()
    def numberedSignature: NumberedString    = v.getNumberedSubSignature
    def paramLocals: Seq[Local]              = for (i <- 0 until v.getParameterCount; b <- v.bodyOpt) yield b.getParameterLocal(i)
  }

  // ── SootMethodRef ───────────────────────────────────────────────────────────

  extension (v: SootMethodRef) {
    def isClinit: Boolean          = v.getName == "<clinit>"
    def signature: String          = v.getSignature
    def subSignature: String       = v.getSubSignature.getString
    def paramTypes: Iterable[Type] = v.getParameterTypes.asScala
  }

  // ── Trap ────────────────────────────────────────────────────────────────────

  extension (v: Trap) {
    def beginUnit: SootUnit               = v.getBeginUnit
    def beginUnit_=(u: SootUnit): Unit    = v.setBeginUnit(u)
    def beginStmt: Stmt                   = v.getBeginUnit.asInstanceOf[Stmt]
    def endUnit: SootUnit                 = v.getEndUnit
    def endUnit_=(u: SootUnit): Unit      = v.setEndUnit(u)
    def endStmt: Stmt                     = v.getEndUnit.asInstanceOf[Stmt]
    def exception: SootClass              = v.getException
    def exception_=(sc: SootClass): Unit  = v.setException(sc)
    def handlerUnit: SootUnit             = v.getHandlerUnit
    def handlerUnit_=(u: SootUnit): Unit  = v.setHandlerUnit(u)
    def handlerStmt: Stmt                 = v.getHandlerUnit.asInstanceOf[Stmt]
  }

  // ── Body ────────────────────────────────────────────────────────────────────

  extension (v: Body) {
    def units: Chain[SootUnit]              = v.getUnits
    def statements: PatchingChain[Stmt]     = v.getUnits.asInstanceOf[PatchingChain[Stmt]]
    def locals: Chain[Local]                = v.getLocals
    def method: SootMethod                  = v.getMethod
    def thisLocal: Option[Local]            = Try(v.getThisLocal).toOption
    def parameterLocal(i: Int): Local       = v.getParameterLocal(i)
    def traps: Chain[Trap]                  = v.getTraps
    def parameterLocals: Iterable[Local]    = v.getParameterLocals.asScala
    def sources: String = v.getUnits.asScala
      .map(it => s"  ${it.toString()} // L${it.lineNumberOpt.getOrElse("0")}")
      .mkString(s"$v.getMethod {\n", "\n", "\n}")
  }

  // ── Stmt ────────────────────────────────────────────────────────────────────

  object SStmt {
    def unapply(stmt: Stmt): Option[(Option[InvokeExpr], Option[ArrayRef], Option[FieldRef])] =
      Some(stmt.invokeExprOpt, stmt.arrayRefOpt, stmt.fieldRefOpt)
  }

  extension (v: Stmt) {
    def invokeExpr: InvokeExpr              = v.getInvokeExpr
    def invokeExprOpt: Option[InvokeExpr]   = ifToOption(v.containsInvokeExpr(), v.getInvokeExpr)
    def arrayRef: ArrayRef                  = v.getArrayRef
    def arrayRefOpt: Option[ArrayRef]       = ifToOption(v.containsArrayRef(), v.getArrayRef)
    def fieldRef: FieldRef                  = v.getFieldRef
    def fieldRefOpt: Option[FieldRef]       = ifToOption(v.containsFieldRef(), v.getFieldRef)
  }

  // ── IfStmt ──────────────────────────────────────────────────────────────────

  object SIfStmt {
    def unapply(stmt: IfStmt): Option[(Value, Stmt)] = Some(stmt.condition, stmt.target)
  }

  extension (v: IfStmt) {
    def condition: Value = v.getCondition
    def target: Stmt     = v.getTarget
  }

  // ── BinopExpr ───────────────────────────────────────────────────────────────

  object SBinopExpr {
    def unapply(expr: BinopExpr): Option[(Value, Value)] = Some(expr.left, expr.right)
  }

  extension (v: BinopExpr) {
    def left: Value  = v.getOp1
    def right: Value = v.getOp2
  }

  object SEqExpr {
    def unapply(exp: EqExpr): Option[(Value, Value)] = Some(exp.left, exp.right)
  }

  // ── FastHierarchy ───────────────────────────────────────────────────────────

  extension (v: FastHierarchy) {
    def abstractDispatch(sm: SootMethod)    = v.resolveAbstractDispatch(sm.getDeclaringClass, sm).asScala.toSet
    def interfaceImplementers(sc: SootClass) = if (sc.isInterface) v.getAllImplementersOfInterface(sc).asScala.toSet else Set[SootClass]()
    def subClassesOf(sc: SootClass)         = v.getSubclassesOf(sc).asScala.toSet
    def allSubinterfaces(sc: SootClass)     = v.getAllSubinterfaces(sc).asScala.toSet
  }

  // ── Scene ───────────────────────────────────────────────────────────────────

  extension (v: Scene) {
    def applicationClasses: Iterable[SootClass]   = v.getApplicationClasses.asScala
    def classes: Iterable[SootClass]              = v.getClasses.asScala
    def libraryClasses: Iterable[SootClass]        = v.getLibraryClasses.asScala
    def phantomClasses: Iterable[SootClass]        = v.getPhantomClasses.asScala
    def field(spec: String): SootField             = v.getField(spec)
    def fieldOpt(spec: String): Option[SootField]  = ifToOption(v.containsField(spec), v.getField(spec))
    def fieldRef(spec: String): SootFieldRef       = v.getField(spec).makeRef()
    def fieldRefOpt(spec: String): Option[SootFieldRef] = ifToOption(v.containsField(spec), v.getField(spec).makeRef())
    def refType(name: String): RefType             = v.getRefType(name)
    def refTypeOpt(name: String): Option[RefType]  = ifToOption(v.containsType(name), v.getRefType(name))
    def sootClass(name: String): SootClass         = v.getSootClass(name)
    def sootClassOpt(name: String): Option[SootClass] = Option(v.getSootClassUnsafe(name))
    def method(sig: String): SootMethod            = v.getMethod(sig)
    def methodOpt(sig: String): Option[SootMethod] = ifToOption(v.containsMethod(sig), v.getMethod(sig))
    def methodRef(sig: String): SootMethodRef      = v.getMethod(sig).makeRef()
    def methodRefOpt(sig: String): Option[SootMethodRef] = ifToOption(v.containsMethod(sig), v.getMethod(sig).makeRef())
    def objectType: RefType                        = v.getObjectType
    def objectClass: SootClass                     = v.getObjectType.getSootClass
    def hierarchy: Hierarchy                       = v.getActiveHierarchy
    def hierarchy_=(h: Hierarchy): Unit            = v.setActiveHierarchy(h)
    def fastHierarchy: FastHierarchy               = v.getOrMakeFastHierarchy
    def fastHierarchy_=(fh: FastHierarchy): Unit   = v.setFastHierarchy(fh)
    def callGraph: CallGraph                       = v.getCallGraph
    def callGraph_=(cg: CallGraph): Unit           = v.setCallGraph(cg)
    def contextNumberer: Numberer[Context]         = v.getContextNumberer
    def contextNumberer_=(cn: Numberer[Context]): Unit = v.setContextNumberer(cn)
    def contextSensitiveCallGraph: ContextSensitiveCallGraph = v.getContextSensitiveCallGraph
    def contextSensitiveCallGraph_=(cscg: ContextSensitiveCallGraph): Unit = v.setContextSensitiveCallGraph(cscg)
    def defaultThrowAnalysis: ThrowAnalysis        = v.getDefaultThrowAnalysis
    def defaultThrowAnalysis_=(ta: ThrowAnalysis): Unit = v.setDefaultThrowAnalysis(ta)
    def entryPoints: Iterable[SootMethod]          = v.getEntryPoints.asScala
    def entryPoints_=(ep: Seq[SootMethod]): Unit   = v.setEntryPoints(ep.asJava)
    def mainClass: SootClass                       = v.getMainClass
    def mainClass_=(sc: SootClass): Unit           = v.setMainClass(sc)
    def mainMethod: SootMethod                     = v.getMainMethod
    def mainMethod_=(sm: SootMethod): Unit         = v.setMainClass(sm.getDeclaringClass)
    def phantomRefs: Boolean                       = v.getPhantomRefs
    def phantomRefs_=(flag: Boolean): Unit         = v.setPhantomRefs(flag)
    def pkgList: Iterable[String]                  = v.getPkgList.asScala
    def pkgList_=(pl: Seq[String]): Unit           = v.setPkgList(pl.asJava)
    def pta: PointsToAnalysis                      = v.getPointsToAnalysis
    def pointsToAnalysis: PointsToAnalysis         = v.getPointsToAnalysis
    def pointsToAnalysis_=(p: PointsToAnalysis): Unit = v.setPointsToAnalysis(p)
    def pag: PAG                                   = v.getPointsToAnalysis.asInstanceOf[PAG]
    def sootClassPath: String                      = v.getSootClassPath
    def sootClassPath_=(scp: String): Unit         = v.setSootClassPath(scp)
    def reachableMethods: ReachableMethods         = v.getReachableMethods
    def reachableMethods_=(rm: ReachableMethods): Unit = v.setReachableMethods(rm)
    def sideEffectAnalysis: SideEffectAnalysis     = v.getSideEffectAnalysis
    def sideEffectAnalysis_=(sea: SideEffectAnalysis): Unit = v.setSideEffectAnalysis(sea)
    def reservedNames: Set[String]                 = v.getReservedNames.asScala.toSet
  }

  // ── Chain ───────────────────────────────────────────────────────────────────

  class RichChain[E](val v: Chain[E]) extends Iterable[E] {
    def ++=(elems: Seq[E]): Unit       = v.addAll(elems.asJava)
    def +=(elem: E): Unit              = v.addLast(elem)
    override def iterator: Iterator[E] = v.iterator().asScala
  }

  given [E]: Conversion[Chain[E], RichChain[E]] = RichChain(_)

  // ── Host ────────────────────────────────────────────────────────────────────

  extension (v: Host) {
    def tags: Iterable[Tag]                       = v.getTags.asScala
    def tag(name: String): Tag                    = v.getTag(name)
    def tagOpt(name: String): Option[Tag]         = Option(v.getTag(name))
    def tagOpt[T <: Tag](typ: Class[T]): Option[T] = v.getTags.asScala.find(_.getClass eq typ).map(_.asInstanceOf[T])
    def lineNumber: Int                           = v.getJavaSourceStartLineNumber
    def lineNumberOpt: Option[Int]                = v.getJavaSourceStartLineNumber match {
      case -1  => None
      case any => Some(any)
    }
  }

  // ── VisibilityAnnotationTag ─────────────────────────────────────────────────

  object SVisibilityAnnotationTag {
    def apply(annotations: AnnotationTag*): VisibilityAnnotationTag = {
      val tag = new VisibilityAnnotationTag(0)
      annotations.foreach(tag.addAnnotation)
      tag
    }
    def apply(annotations: Iterable[AnnotationTag]): VisibilityAnnotationTag = {
      val tag = new VisibilityAnnotationTag(0)
      annotations.foreach(tag.addAnnotation)
      tag
    }
    def unapply(vat: VisibilityAnnotationTag) = vat.getAnnotations.asScala
  }

  extension (v: VisibilityAnnotationTag) {
    def annotations: Iterable[AnnotationTag] = v.getAnnotations.asScala
  }

  // ── AnnotationTag ───────────────────────────────────────────────────────────

  object SAnnotationTag {
    def apply(name: String, elements: Seq[AnnotationElem] = Seq()) = new AnnotationTag(name, elements.asJava)
    def unapply(at: AnnotationTag) = Some(at.getName, at.getInfo, at.getElems.asScala)
  }

  object SAnnotationStringElem {
    def apply(name: String, value: String) = new AnnotationStringElem(value, 's', name)
  }

  extension (v: AnnotationTag) {
    def elements: Iterable[AnnotationElem] = v.getElems.asScala
    def info: String                       = v.getInfo
    def name: String                       = v.getName
  }

  // ── AnnotationElem ──────────────────────────────────────────────────────────

  object SAnnotationElem {
    def unapply(ae: AnnotationElem) = Some(ae.getName, ae.getKind)
  }

  extension (v: AnnotationElem) {
    def kind: Char   = v.getKind
    def name: String = v.getName
  }

  // ── Value ───────────────────────────────────────────────────────────────────

  extension (v: Value) {
    def useBoxes: Seq[ValueBox] = v.getUseBoxes.asScala.toSeq
  }

  // ── InvokeExpr ──────────────────────────────────────────────────────────────

  object SInvokeExpr {
    def unapply(expr: InvokeExpr) = expr match {
      case SStaticInvokeExpr(args, method)         => Some(None, args, method)
      case SInstanceInvokeExpr(base, args, method) => Some(Some(base), args, method)
      case _                                       => throw new RuntimeException("Unhandled invoke expression type")
    }
  }

  extension (v: InvokeExpr) {
    def args: Iterable[Value]         = v.getArgs.asScala
    def arg(index: Int): Value        = v.getArg(index)
    def argCount: Int                 = v.getArgCount
    def method: SootMethod            = v.getMethod
    def methodOpt: Option[SootMethod] = Try(Option(v.getMethod)).getOrElse(None)
    def methodRef: SootMethodRef      = v.getMethodRef
    def returnType: Type              = v.getType
  }

  // ── StaticInvokeExpr ────────────────────────────────────────────────────────

  object SStaticInvokeExpr {
    def apply(args: Seq[Value], target: SootMethod): StaticInvokeExpr =
      Jimple.v.newStaticInvokeExpr(target.makeRef(), args.asJava)
    def unapply(expr: StaticInvokeExpr) = Some(expr.getArgs.asScala, expr.getMethod)
  }

  // ── InstanceInvokeExpr ──────────────────────────────────────────────────────

  object SInstanceInvokeExpr {
    def apply(base: Local, args: Seq[Value], target: SootMethod): InstanceInvokeExpr =
      target.getDeclaringClass match {
        case iface if iface.isInterface => Jimple.v.newInterfaceInvokeExpr(base, target.makeRef(), args.asJava)
        case _                          => Jimple.v.newVirtualInvokeExpr(base, target.makeRef(), args.asJava)
      }
    def unapply(expr: InstanceInvokeExpr) = Some(expr.getBase, expr.getArgs.asScala, expr.getMethod)
  }

  extension (v: InstanceInvokeExpr) {
    def base: Value = v.getBase
  }

  // ── Local ───────────────────────────────────────────────────────────────────

  object SLocal {
    def unapply(l: Local): Option[(String, Type)] = Some(l.getName, l.getType)
  }

  extension (v: Local) {
    def name: String              = v.getName
    def name_=(n: String): Unit   = v.setName(n)
  }

  // ── ArrayRef ────────────────────────────────────────────────────────────────

  object SArrayRef {
    def unapply(ar: ArrayRef): Option[(Value, Value)] = Some(ar.getBase, ar.getIndex)
  }

  extension (v: ArrayRef) {
    def base: Value        = v.getBase
    def baseBox: ValueBox  = v.getBaseBox
    def index: Value       = v.getIndex
    def indexBox: ValueBox = v.getIndexBox
  }

  // ── FieldRef ────────────────────────────────────────────────────────────────

  object SFieldRef {
    def apply(sf: SootField): SootFieldRef   = sf.makeRef()
    def unapply(fr: FieldRef): Option[SootField] = Some(fr.getField)
  }

  extension (v: FieldRef) {
    def field: SootField                     = v.getField
    def fieldRef: SootFieldRef               = v.getFieldRef
    def fieldRef_=(sfr: SootFieldRef): Unit  = v.setFieldRef(sfr)
  }

  object SStaticFieldRef {
    def apply(sf: SootField): SootFieldRef        = sf.makeRef()
    def unapply(fr: StaticFieldRef): Option[SootField] = Some(fr.getField)
  }

  // ── CastExpr ────────────────────────────────────────────────────────────────

  object SCastExpr {
    def unapply(ce: CastExpr): Option[(Value, Type)] = Some(ce.getOp, ce.getCastType)
  }

  extension (v: CastExpr) {
    def op: Value                        = v.getOp
    def op_=(newOp: Value): Unit         = v.setOp(newOp)
    def opBox: ValueBox                  = v.getOpBox
    def castType: Type                   = v.getCastType
    def castType_=(ct: Type): Unit       = v.setCastType(ct)
  }

  // ── DefinitionStmt ──────────────────────────────────────────────────────────

  object SDefinitionStmt {
    def unapply(ds: DefinitionStmt): Option[(Value, Value)] = Some(ds.getLeftOp, ds.getRightOp)
  }

  extension (v: DefinitionStmt) {
    def leftOp: Value    = v.getLeftOp
    def leftOpBox: ValueBox = v.getLeftOpBox
    def rightOp: Value   = v.getRightOp
    def rightOpBox: ValueBox = v.getRightOpBox
  }

  // ── IdentityStmt ────────────────────────────────────────────────────────────

  object SIdentityStmt {
    def unapply(is: IdentityStmt): Option[(Value, Value)] = Some(is.getLeftOp, is.getRightOp)
  }

  object SInstanceFieldRef {
    def unapply(r: InstanceFieldRef) = Some(r.getBase, r.getField)
  }

  object SNewExpr {
    def unapply(e: NewExpr) = Some(e.getBaseType)
  }

  // ── AssignStmt ──────────────────────────────────────────────────────────────

  object SAssignStmt {
    def apply(left: Value, right: Value): AssignStmt = Jimple.v.newAssignStmt(left, right)
    def unapply(as: AssignStmt): Option[(Value, Value)] = Some(as.getLeftOp, as.getRightOp)
  }

  extension (v: AssignStmt) {
    def rightOp_=(ro: Value): Unit = v.setRightOp(ro)
    def leftOp_=(lo: Value): Unit  = v.setLeftOp(lo)
  }

  // ── ReturnStmt ──────────────────────────────────────────────────────────────

  object SReturnStmt {
    def unapply(rs: ReturnStmt): Option[Value] = Some(rs.getOp)
  }

  extension (v: ReturnStmt) {
    def op: Value              = v.getOp
    def op_=(o: Value): Unit   = v.setOp(o)
  }

  // ── Options ─────────────────────────────────────────────────────────────────

  extension (v: Options) {
    def classPath: String                      = v.soot_classpath()
    def classPath_=(cp: String): Unit          = v.set_soot_classpath(cp)
    def classPath_=(cp: Seq[Path]): Unit       = v.set_soot_classpath(cp.mkString(File.pathSeparator))
    def processPath: Seq[String]               = v.process_dir().asScala.toSeq
    def processPath_=(pp: Seq[String]): Unit   = v.set_process_dir(pp.asJava)
    def allowPhantomRefs: Boolean              = v.allow_phantom_refs()
    def allowPhantomRefs_=(b: Boolean): Unit   = v.set_allow_phantom_refs(b)
    def androidJars: String                    = v.android_jars()
    def androidJars_=(s: String): Unit         = v.set_android_jars(s)
    def inAppMode: Boolean                     = v.app()
    def inAppMode_=(b: Boolean): Unit          = v.set_app(b)
    def wholeProgram: Boolean                  = v.whole_program()
    def wholeProgram_=(b: Boolean): Unit       = v.set_whole_program(b)
    def mainClass: String                      = v.main_class()
    def mainClass_=(mc: String): Unit          = v.set_main_class(mc)
    def outputDir: String                      = v.output_dir()
    def outputDir_=(s: String): Unit           = v.set_output_dir(s)
    def outputDir_=(p: Path): Unit             = v.set_output_dir(p.toAbsolutePath.toString)
    def outputFormat: Int                      = v.output_format()
    def outputFormat_=(i: Int): Unit           = v.set_output_format(i)
    def srcPrec: Int                           = v.src_prec()
    def srcPrec_=(i: Int): Unit                = v.set_src_prec(i)
    def keepLineNumber: Boolean                = v.keep_line_number()
    def keepLineNumber_=(b: Boolean): Unit     = v.set_keep_line_number(b)
    def prependClassPath: Boolean              = v.prepend_classpath()
    def prependClassPath_=(b: Boolean): Unit   = v.set_prepend_classpath(b)
    def fullResolver: Boolean                  = v.full_resolver()
    def fullResolver_=(b: Boolean): Unit       = v.set_full_resolver(b)
  }

  // ── Constant factories ──────────────────────────────────────────────────────

  object SStringConstant { def apply(s: String) = StringConstant.v(s) }
  object SIntConstant    { def apply(i: Int)    = IntConstant.v(i)    }
  object SLongConstant   { def apply(l: Long)   = LongConstant.v(l)   }
  object SDoubleConstant { def apply(d: Double) = DoubleConstant.v(d) }
  object SFloatConstant  { def apply(f: Float)  = FloatConstant.v(f)  }
}
