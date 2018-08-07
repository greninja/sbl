package elegans

object Constraints {
  import Cells._
  import Model._
  import Schedules._
  import Experiments._
  import TimerSemantics._
  
  import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}
  import scala.collection.mutable.ListBuffer
  

  import java.io._

  import z3.scala._
  import z3.scala.dsl._

  import TimerLogic._

  private var ctx_ : Z3Context = null
  private var solver_ : Z3Solver = null
  private var portVars_   = MutableMap[Int, MutableMap[Port, Z3AST]]()
  private var channelVars = MutableMap[Int, MutableMap[(Cell, Cell), Z3AST]]()

  //Maps to store non-deterministic variables from first run
  private var scheduleSolutionReference = MutableMap[Int, MutableMap[Int, Z3AST]]()
  private var AcHypValueReference = MutableMap[Int, MutableMap[Int, Seq[Z3AST]]]()
  
  //Maps from tracking variables to non-deterministic variables and their values
  private var trackScheduleVarsMap = MutableMap[Z3AST, (Z3AST, Configuration)]()
  private var trackAcHypVarsMap = MutableMap[Z3AST, (Z3AST, Int)]()
  private var trackLsVarsMap    = MutableMap[Z3AST, (Z3AST, Z3AST)]()

  private var globalASTconstraints = Seq[Z3AST]()
  private var interCellchannel = Seq[(Cell, Cell)]()

  //To store all the variables causing UNSAT across all iterations of loop
  var important_schedule = MutableSet[(String, Configuration)]()
  var important_achyp    = MutableSet[(String, Int)]()
  var important_ls       = MutableSet[(String, String)]()

  private var important = MutableSet[Z3AST]()

  def ctx       = ctx_
  def solver    = solver_
  def portVars  = portVars_

  private var semantics = List(TimerSemantics, StatefulSemantics)

  val translationProfiler   = new Stopwatch("translation", true)
  val synthesisProfiler     = new Stopwatch("z3-synthesis", true)
  val verificationProfiler  = new Stopwatch("z3-verification", true)
  val runningProfiler       = new Stopwatch("z3-run-symbolic", true)

  private def intSort() = Settings.bitvectorWidth match {
    case Some(width) => ctx.mkBVSort(width)
    case None => ctx.mkIntSort
  }

  private def disabled()      = ctx.mkInt(0, intSort())
  private def rightEnabled()  = ctx.mkInt(1, intSort())
  private def leftEnabled()   = ctx.mkInt(2, intSort())

  private def config2ast(c: Configuration) : Z3AST = c match {
      case Disabled => disabled()
      case EnabledRight => rightEnabled()
      case EnabledLeft => leftEnabled()
    }

  private var schedulesExperimentsCells = 
    MutableMap[CoarseSchedule, MutableMap[Experiment, List[Cell]]]()

  type History = MutableMap[Int, MutableMap[Port, Boolean]]
  type StringHistory = MutableMap[Int, MutableMap[String, Boolean]]
  type AcHypValuesMap = MutableMap[Int, MutableMap[Int, Seq[Int]]]
  type LsValuesMap = MutableMap[Int, Seq[Z3AST]]

  type Solution = Map[String, LogicSolution]
  case class UndefinedHole(id: String) extends Exception

  sealed trait FateAssertionMethod
  case object AssertFateDecision extends FateAssertionMethod
  case object AssertNegatedFateDecision extends FateAssertionMethod
  case object AssertNoFateDecision extends FateAssertionMethod

  def concretize(cells: List[Cell], solution: Solution) {
    for (sem <- semantics)
      sem.concretize(cells, solution)
  }

  /** Extracts port values for each timestep in a run */
  private def modelMap(m: Z3Model, s: CoarseSchedule, e: Experiment): History = {
    val res = MutableMap[Int, MutableMap[Port, Boolean]]()
    for (i <- 0 to s.size) {
      res(i) = MutableMap[Port, Boolean]()
      for (c <- schedulesExperimentsCells(s)(e)) {
        for (n <- c.N) {
          for (p <- n.P) {
            res(i)(p) = m.evalAs[Boolean](portVars(i)(p)) match {
              case Some(value) => value
              case None => 
                // logWarning("Model doesn't define " + p.toString + " at time " + i)
                false
            }
          }
        }
      }
    }
    res
  }

  /** Used by testing framework to compare traces */
  def stringMap(h: History): StringHistory = {
    val ret = MutableMap[Int, MutableMap[String, Boolean]]()
    for ((i, m) <- h) {
      ret(i) = MutableMap[String, Boolean]()
      for ((p, v) <- m) {
        ret(i)(p.toString) = v
      }
    }
    ret
  }


  def assertConstraint(c: Z3AST) {
    solver.assertCnstr(c)
  }

  def assertConstraint(c: Tree[BoolSort]) {
    ctx.assertCnstr(c)
  }

  private def restartZ3() {
    if (ctx != null) ctx.delete
    ctx_ = new Z3Context("model" -> true, "proof"->true, "auto_config"->false)
    solver_ = ctx.mkSolver() 
    //solver_2 = ctx.mkSolver()

    portVars_ = MutableMap[Int, MutableMap[Port, Z3AST]]()
    channelVars = MutableMap[Int, MutableMap[(Cell, Cell), Z3AST]]()
    
    scheduleSolutionReference = MutableMap[Int, MutableMap[Int, Z3AST]]()
    AcHypValueReference = MutableMap[Int, MutableMap[Int, Seq[Z3AST]]]()
    
    trackScheduleVarsMap = MutableMap[Z3AST, (Z3AST, Configuration)]()
    trackAcHypVarsMap = MutableMap[Z3AST, (Z3AST, Int)]()
    trackLsVarsMap   =  MutableMap[Z3AST, (Z3AST, Z3AST)]()
    
    schedulesExperimentsCells = MutableMap[CoarseSchedule, MutableMap[Experiment, List[Cell]]]()
    semantics.map(_.restart())
  }


  /*private def disableInitialVars(cells: List[Cell]) {
    for (c <- cells)
      for (n <- c.N)
        for (p <- n.outputPorts)
          assertConstraint(!portVars(0)(p))
  }*/

  private def assertInitialVars(cells: List[Cell]) {
    for (c <- cells) {
      for (n <- c.N) {
        for (l <- n.logics) {
          l.assertInitialOutputValues()
        }
      }
    }
  }


  private def assertFates(asyncCells: List[Cell], experiment: Experiment, finalIndex: Int, fateAssertionMethod: FateAssertionMethod) {
    
    def exclusiveFate(cell: Cell, fate: String) = {
      val allOutcomes = cell.outcomeBundles.keySet
      
      cell.outcomeBundles.get(fate) match {
        case None => logWarning("No bundle for fate " + fate + " in cell " + cell); ctx.mkTrue
        case Some(bundleSet) => {
          val valueEnabled = bundleSet.foldLeft(ctx.mkFalse) {
            case (ast, bundle) => ctx.mkOr(ast, portVars(finalIndex)(bundle.ports(0)))
          }
         
          val otherOutcomes = allOutcomes - fate
          val othersDisabled = otherOutcomes.foldLeft(ctx.mkTrue) {
            case (ast, otherVal) => {
              val otherValEnabled = cell.outcomeBundles(otherVal).foldLeft(ctx.mkFalse) {
                case (innerAst, otherBundle) => ctx.mkOr(innerAst, portVars(finalIndex)(otherBundle.ports(0)))
              }
              ctx.mkAnd(ast, ctx.mkNot(otherValEnabled))

            }
          }
          ctx.mkAnd(valueEnabled, othersDisabled)
        }
      }
    }
      
    var setoffates = experiment.fates
    var fateofExperiment = Set(setoffates.head) 
    println("Fate is :")
    println(fateofExperiment)

    val fateDisjunction = for (fate <- fateofExperiment) yield {
        val patternConjunction = for ((asyncCell, cellFate) <- asyncCells zip fate) yield {
          exclusiveFate(asyncCell, cellFate)
        }          
      patternConjunction.foldLeft(ctx.mkTrue)(ctx.mkAnd(_, _))
    }

    // if no fate was specified, all fates are OK.
    val fateCnstr = 
      if (fateDisjunction.isEmpty) ctx.mkTrue 
      else fateDisjunction.foldLeft(ctx.mkFalse)(ctx.mkOr(_, _))

    //println("fateconstraint is : ")
    //println(fateCnstr)
    
    fateAssertionMethod match {
      case AssertFateDecision =>
            assertConstraint(fateCnstr)
      case AssertNegatedFateDecision =>
            if (fateDisjunction.isEmpty) logWarning("Verifying against any fate pattern.")
            assertConstraint(ctx.mkNot(fateCnstr)) 
      case AssertNoFateDecision =>
    }
  }

  private def assertExperiments(
      scheduleLength: Int, concreteSchedule: Option[List[MacroStep]], 
      solution: Option[Solution], experiments: Seq[Experiment], 
      fateAssertionMethod: FateAssertionMethod) {
    
    def makePortVars(cell: Cell, scheduleLength: Int) {
      for (idx <- 0 to scheduleLength) {
        portVars(idx) = portVars.getOrElse(idx, MutableMap())
        for (node <- cell.N) {
          for (port <- node.P) {
            portVars(idx)(port) = ctx.mkFreshBoolConst(port.toString + "_" + idx)
          }
        }
      }
    }

    def makeChannelVars(aPrioriChannels: List[(Cell, Cell)], asyncChannels: List[(Cell, Cell)], scheduleLength: Int) {
      for (idx <- 0 until scheduleLength) {
        channelVars(idx) = MutableMap()
        scheduleSolutionReference(idx) = MutableMap()

        for ((c1, c2) <- aPrioriChannels) {
          val channelvariable = ctx.mkFreshConst(c1.toString + "_" + c2.toString + "_channel_" + idx, intSort())
          channelVars(idx)((c1, c2)) = channelvariable 
        }

        for (((c1, c2), j) <- asyncChannels zipWithIndex) {
          val fresh = ctx.mkFreshConst(c1.toString + "_" + c2.toString + "_channel_" + idx, intSort())
          channelVars(idx)((c1, c2)) = fresh
          scheduleSolutionReference(idx)(j) = fresh
        }
      }
    }
  
    def runsAtSameTime(runningCell: Cell, neighborCell: Cell, t: Int): Z3AST = {
      channelVars(t).get((runningCell, neighborCell)) match {
        case Some(cv) => {
          
 
          ctx.mkEq(cv, disabled())
        }
        case None => {
          channelVars(t).get((neighborCell, runningCell)) match {
            case Some(cv) => ctx.mkEq(cv, disabled()) 
            case None => throw new Exception("cannot find channel variable for " + (runningCell, neighborCell))
          }
        }
      }
    }

    def runsBefore(runningCell: Cell, neighborCell: Cell, t: Int): Z3AST = {
      channelVars(t).get((runningCell, neighborCell))  match {
        case Some(cv) => {
          ctx.mkEq(cv, rightEnabled())
        }
        case None => {
          channelVars(t).get((neighborCell, runningCell)) match {
            case Some(cv) => ctx.mkEq(cv, leftEnabled())
            case None => throw new Exception("cannot find channel variable for " + (runningCell, neighborCell))
          }
        }
      }
    }

   def runsAfter(runningCell: Cell, neighborCell: Cell, t: Int): Z3AST = {
      channelVars(t).get((runningCell, neighborCell))  match {
        case Some(cv) => {
          ctx.mkEq(cv, leftEnabled())
        }
        case None => {
          channelVars(t).get((neighborCell, runningCell)) match {
            case Some(cv) => ctx.mkEq(cv, rightEnabled())
            case None => throw new Exception("cannot find channel variable for " + (runningCell, neighborCell))
          }
        }
      }
    }

    def assertInputPort(p: Port, t: Int) {
      var disjuncts = MutableSet[Z3AST]()
      val destCell = p.parent.parent

      for (de <- p.incomingDelayedEdges) {
        val sourcePort = de.source
        val sourceCell = sourcePort.parent.parent
        if (sourceCell == destCell) {
          disjuncts += portVars(t - 1)(sourcePort)
        } else {
          val sameTimePred = ctx.mkAnd(
            runsAtSameTime(destCell, sourceCell, t - 1), 
            portVars(t - 1)(sourcePort))
          val runsBeforePred = ctx.mkAnd(
            runsBefore(destCell, sourceCell, t - 1), 
            portVars(t - 1)(sourcePort))
          val runsAfterPred = ctx.mkAnd(
            runsAfter(destCell, sourceCell, t - 1), 
            portVars(t)(sourcePort))
          disjuncts ++= Set(sameTimePred, runsBeforePred, runsAfterPred)
        }
      }

      for (nde <- p.incomingNonDelayedEdges) {
        val sourcePort = nde.source
        val sourceCell = sourcePort.parent.parent
        if (sourceCell == destCell) {
          disjuncts += portVars(t)(sourcePort)
        } else {
          throw new Exception("todo: intercellular nondelayed edge")
        }
      }

      //println("these are disjuncts")
      //println(disjuncts)

      if (!disjuncts.isEmpty)
        assertConstraint(ctx.mkIff(portVars(t)(p), ctx.mkOr(disjuncts.toList: _*)))
      else {
        // if no incoming edges, input port is false
        assertConstraint(!portVars(t)(p))
      }
    }

    def assertInputPorts(cell: Cell, t: Int) {
      for (n <- cell.N) {
        for (p <- n.inputPorts) {
          assertInputPort(p, t)
        }
      }
    }

    def assertChannelRanges() {
      for ((idx, m) <- channelVars) {
        for ((_, ast) <- m) {
          val disj = ctx.mkOr(
            ctx.mkEq(ast, disabled()),
            ctx.mkEq(ast, rightEnabled()),
            ctx.mkEq(ast, leftEnabled())
          )
          assertConstraint(disj)
        }
      }
    }

    def assertChannelValues(configurations: Map[Int, Map[(Cell, Cell), Configuration]]) {
      for ((t, stepConfigs) <- configurations) {
        for (((c1, c2), config) <- stepConfigs) {
          val channelVar = channelVars(t)((c1, c2))
          val toAssert = ctx.mkEq(channelVar, config2ast(config))
          assertConstraint(toAssert)
          }
      }
    }

    def assertExperiment(experiment: Experiment, fateAssertionMethod: FateAssertionMethod) {
      val (alwaysRunningCells, aPrioriChannels, asyncCells) = createSystem(experiment)
   
      val allCells = alwaysRunningCells ::: asyncCells

      solution match {
        case Some(sol) => 
          concretize(allCells, sol)
        case None =>
      }

      // create port variables variables
      for (cell <- allCells) {
        makePortVars(cell, scheduleLength)
      }

      // let semantics initialize their work
      for (s <- semantics)
        s.initializeConstraints(allCells, scheduleLength)

      // disableInitialVars(allCells)
      assertInitialVars(allCells)

      val asyncChannelBuffer = new ListBuffer[(Cell, Cell)]()
      asyncCells.reduceLeft[Cell] {
        case (left, right) =>
          asyncChannelBuffer append ((left, right))
          right
      }
      
      val interAsyncCellChannels = asyncChannelBuffer.toList
      interCellchannel = interAsyncCellChannels

      //println("interAsyncCellChannels are : ")
      //println(interAsyncCellChannels)

      // create channel variables in solver and restrict their range
      makeChannelVars(aPrioriChannels, interAsyncCellChannels, scheduleLength)
      assertChannelRanges()

      // Block 1
      for (t <- 0 until scheduleLength) {
        AcHypValueReference(t+1) = MutableMap()
        var counter = 0
        for (c <- allCells) {
          assertInputPorts(c, t + 1)
          for (n <- c.N) {
            for (l <- n.logics) {  
                  if (l.id == "let23#1") {
                    val vars = l.assertLogic(t+1)
                    counter += 1
                    AcHypValueReference(t+1)(counter) = vars.get
                  }
                  else{
                    l.assertLogic(t+1)
                  }
              }
            }
          }
      }
      
      // schedule for always-running cells are asserted for both synthesis and verification
      val aPrioriChannelsMap = 
        (aPrioriChannels map (a => (a, EnabledRight))).toMap[(Cell, Cell), Configuration]
      val aPrioriConfigsPerStep = (0 until scheduleLength) map (t => (t, aPrioriChannelsMap))
      assertChannelValues(aPrioriConfigsPerStep.toMap)

      // if we have a concrete schedule, assert it. 
      concreteSchedule match {
        case Some(macroSteps) => {
          val mapsPerStep = for ((macroStep, t) <- macroSteps zipWithIndex) yield {
            val interAsyncCellChannelsMap = (interAsyncCellChannels zip macroStep).toMap
            (t, interAsyncCellChannelsMap)
          }
          assertChannelValues(mapsPerStep.toMap)
          
          schedulesExperimentsCells(macroSteps) = schedulesExperimentsCells.getOrElse(macroSteps, MutableMap[Experiment, List[Cell]]())
          schedulesExperimentsCells(macroSteps)(experiment) = allCells
        }
        case None =>
      }

      assertFates(asyncCells, experiment, scheduleLength, fateAssertionMethod)
    }

    for (experiment <- experiments) {
      assertExperiment(experiment, fateAssertionMethod)
    }
  }

  /** Reconstructs a schedule from a Z3 model */
  private def recoverSchedule(m: Z3Model): CoarseSchedule = {
    def configFromModel(ast: Z3AST): Configuration = m.evalAs[Int](ast) match {
      case Some(i) => {
        if (i == 0)
          Disabled
        else if (i == 1)
          EnabledRight
        else if (i == 2)
          EnabledLeft
        else
          terminate("bad channel configuration valuation")
      }
      case None => {
        terminate("no value for channel configuration")
      }
    }

    val steps = for (i <- 0 until scheduleSolutionReference.size) yield {
      val stepMap = scheduleSolutionReference(i)
      val step = for (j <- 0 until stepMap.size) yield {
        configFromModel(stepMap(j))
      }
      step.toList
    }
    steps.toList
  }

  /* Recovering the input strenghts of AC and Hyp signal, for each timestep for each cell, from
   the first run in order to fix them in the second run*/
  private def recoverAcHypValues(m : Z3Model) : AcHypValuesMap = {
    def valueFromModel(ast : Z3AST) : Int = m.evalAs[Int](ast) match {
        case Some(i) => i
        case None => terminate("No value for the given AC-HYP variable")
    }

    val varmap = MutableMap[Int, MutableMap[Int, Seq[Int]]]()
    for (timestep <- 1 to AcHypValueReference.size) {
        varmap(timestep) = MutableMap()
        for(cellid <- 1 to nbAsyncCells) {
           val seqt = AcHypValueReference(timestep)(cellid)
           val listvalues = for (i <- 0 until seqt.size) yield {
            valueFromModel(seqt(i))
           }
           varmap(timestep)(cellid) = listvalues.toList
          }
        }
      varmap
  }

  /* Recovering the non deterministic values of VPC_1_ls_left and VPC_6_ls_right */
  def recoverLsValues(m : Z3Model) : LsValuesMap = {
    def valueFromModel(ast : Z3AST) : Z3AST = m.eval(ast) match {
      case Some(b) => b
      case None => terminate("No value given for the ls variable : " + ast.toString)
    }

    val varmap = MutableMap[Int, Seq[Z3AST]]()
    for (t <- 1 to lsVarsRef.size) {
      val listofVars = lsVarsRef(t)
      val listvalues = for (i <- 0 until listofVars.size) yield {
        valueFromModel(listofVars(i))
      }
      varmap(t) = listvalues.toList
    }
    varmap
  }
  
  /** Synthesizes values for the hole values */
  def synthesize(
      inputs: Set[(CoarseSchedule, Experiment)],
      toSeeInSomeRun:   Set[(Experiment, Option[CoarseSchedule])],
      toAvoidInSomeRun: Set[(Experiment, Option[CoarseSchedule])]): Option[Solution] = {
    
    restartZ3()

    log("Solving for " + inputs.size + " input pairs.")

    translationProfiler.start

    val scheduleSet = inputs.map(_._1)

    for (sched <- scheduleSet) {
      val experiments = inputs.filter(_._1 == sched).map(_._2).toList
      log("Schedule: ")
      log((sched map (step => step.mkString(" "))).mkString("\n"))
      log("Experiments:")
      log(experiments.mkString("\n"))
      assertExperiments(sched.size, Some(sched), None, experiments, AssertFateDecision)
    }

    for ((exp, sched) <- toSeeInSomeRun) {
      val schedString = if (sched.isDefined) "a specific" else "some"
      log("Expecting to see in " + schedString + " run:")
      log(exp)
      assertExperiments(Settings.runLength, sched, None, 
        List(exp), AssertFateDecision)
    }

    for ((exp, sched) <- toAvoidInSomeRun) {
      val schedString = if (sched.isDefined) "a specific" else "some"
      log("Expecting to avoid in " + schedString + " run:")
      log(exp)
      assertExperiments(Settings.runLength, sched, None, 
        List(exp), AssertNegatedFateDecision)
    }

    for (s <- semantics)
      s.finalizeConstraints()
    
    translationProfiler.stop

    log("Invoking Z3.")
    synthesisProfiler.start
    Statistics.solverCalled()
    ctx.checkAndGetModel match {
      case (Some(true), m) => {
        Statistics.solverReturned()
        synthesisProfiler.stop
        
        println("the model:")
        println(m)

        var recovered = Map[String, LogicSolution]()
        for (sem <- semantics)
          recovered ++= sem.solution(m)

        m.delete

        Some(recovered)
      }
      case _ => {
        Statistics.solverReturned()
        synthesisProfiler.stop
        None
      }
    }
  }

  def enumerateForInput(
      inputs: Set[(CoarseSchedule, Experiment)],
      toSeeInSomeRun:   Set[(Experiment, Option[CoarseSchedule])],
      toAvoidInSomeRun: Set[(Experiment, Option[CoarseSchedule])],
      maxNbModels: Int): Set[Solution] = {
    restartZ3()

    log("Starting enumeration.")

    val scheduleSet = inputs.map(_._1)

    translationProfiler.start

    for (sched <- scheduleSet) {
      val experiments = inputs.filter(_._1 == sched).map(_._2).toList
      assertExperiments(sched.size, Some(sched), None, experiments, AssertFateDecision)
    }
    
    for ((exp, sched) <- toSeeInSomeRun) {
      val schedString = if (sched.isDefined) "a specific" else "some"
      log("Expecting to see in " + schedString + " run:")
      log(exp)
      assertExperiments(Settings.runLength, sched, None, 
        List(exp), AssertFateDecision)
    }

    for ((exp, sched) <- toAvoidInSomeRun) {
      val schedString = if (sched.isDefined) "a specific" else "some"
      log("Expecting to avoid in " + schedString + " run:")
      log(exp)
      assertExperiments(Settings.runLength, sched, None, 
        List(exp), AssertNegatedFateDecision)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
    }

    for (s <- semantics)
      s.finalizeConstraints()

    translationProfiler.stop

    log("Invoking Z3.")
    synthesisProfiler.start

    var solutionSet = Set[Solution]()

    Statistics.solverCalled()
    val models = ctx.checkAndGetAllModels.take(maxNbModels)
    Statistics.solverReturned()

    for (m <- models) {
      log("Found one model.")
      synthesisProfiler.stop

      var recovered = Map[String, LogicSolution]()
      for (sem <- semantics)
        recovered ++= sem.solution(m)

      solutionSet += recovered
      synthesisProfiler.start

      log("Re-invoking Z3.")
      m.delete
    }

    solutionSet
  }

  /** Verifies whether the hole values verify the given experiment for all
   * schedules. 
   *
   * @return `None` if there are no counterexamples, a counterexample schedule
   * otherwise. 
   */
  
  def synthesizeSchedule(experiment : Experiment, solution : Option[Solution])  = {

   //Generating a solution as we do not want holes for our purpose (schedulesummarization)
   //val sol = synthesizeHolesForScheduleSummarization(experiment)
   //println("this is solution")
   //println(sol)   

   // This is to generate a schedule for a particular fate 
   restartZ3()
   assertExperiments(Settings.runLength, None, None, List(experiment), AssertFateDecision)
   var iterCount = 0

   /*val assertions1 = solver.getAssertions().toSeq
   // Writing the assertions in the solver to a file for debugging if necessary
   val file = new File("Assertions1_10TimeSteps")
   val bw = new BufferedWriter(new FileWriter(file))
   bw.write(assertions1.toString)
   //bw2.write(cexSchedule.toString)
   bw.close()*/

   while(solver.check == Some(true)) {

     // Increasing the counter to keep a track of iterations required to converge
     iterCount += 1

     //Getting the model
     val model = solver.getModel

     // Writing the output to a file
     val file1 = new File("Model1_10TimeSteps")
     val bw1 = new BufferedWriter(new FileWriter(file1))
     bw1.write(model.toString)
     bw1.close()

     //Extracting the Ac-Hyp values
     val AcHypExtractedValues = recoverAcHypValues(model)
   
     //Extracting the Ls values
     val LsExtractedValues = recoverLsValues(model)

     // Extracting the schedule from the generated model
     val cexSchedule = recoverSchedule(model)

     /* Asserting the experiment with negated fate and tracking :
          (1) extracted schedule 
          (2) extracted AC & Hyp input strengths
          (3) extracted Ls values
     */
     
     restartZ3()
     assertExperiments(Settings.runLength, None, None, List(experiment), AssertNegatedFateDecision)
     
     // Tracking the schedule variables 
     cexSchedule match {
        case Some(macroSteps) => {
          val mapsPerStep = for ((macroStep, t) <- macroSteps zipWithIndex) yield {
            val interCellChannelsMap = (interCellchannel zip macroStep).toMap
            (t, interCellChannelsMap)
          }
           
          for ((t, stepConfigs) <- mapsPerStep.toMap) {
              var counter = 0
              for (((c1, c2), config) <- stepConfigs) {
                  counter += 1
                  val astconfig = config2ast(config)
                  val channelVar = channelVars(t)((c1, c2))
                  val toAssert = ctx.mkEq(channelVar, astconfig)
                  val tvar = ctx.mkBoolConst("trSch"+"_"+t+"_"+counter)
                  trackScheduleVarsMap(tvar) = (channelVar, config)
                  assertConstraint(ctx.mkImplies(tvar, toAssert))
              }
            }  
          }
        case None => 
     }

     // Track AC-Hyp values 
     for (timestep <- 1 to AcHypValueReference.size) {
      for (cellid <- 1 to nbAsyncCells) {
          for (s <- 0 until 2) {
            val astvariable = AcHypValueReference(timestep)(cellid)(s)
            val intvariable = AcHypExtractedValues(timestep)(cellid)(s)
            val toAssert = ctx.mkEq(astvariable, ctx.mkInt(intvariable, ctx.mkIntSort))

            val trvar = ctx.mkBoolConst("trAcHyp"+"_"+timestep+"_"+cellid+"_"+s)
            assertConstraint(ctx.mkImplies(trvar, toAssert))

            trackAcHypVarsMap(trvar) = (astvariable, intvariable)
          }
        }
     }

     // Track ls_left for VPC_1 and ls_right for VPC_6
     for (timestep <- 1 to lsVarsRef.size) {
      for (s <- 0 until 2) {
        val astvariable = lsVarsRef(timestep)(s)
        val boolvariable = LsExtractedValues(timestep)(s)
        if (ctx.isEqAST(boolvariable, ctx.mkTrue)) {
          val toAssert = ctx.mkEq(astvariable, ctx.mkTrue)

          val trvar = ctx.mkBoolConst("trLs"+"_"+timestep+"_"+s)
          assertConstraint(ctx.mkImplies(trvar, toAssert))  
          trackLsVarsMap(trvar) = (astvariable, boolvariable)  
        } else {
          val toAssert = ctx.mkEq(astvariable, ctx.mkFalse)
          
          val trvar = ctx.mkBoolConst("trLs"+"_"+timestep+"_"+s)
          assertConstraint(ctx.mkImplies(trvar, toAssert))
          trackLsVarsMap(trvar) = (astvariable, boolvariable)  
        }
      }
     }

     /*val assertions2 = solver.getAssertions().toSeq
     // Writing the assertions in the solver to a file for debugging if necessary
     val file2 = new File("Assertions2_10TimeSteps")
     val bw2 = new BufferedWriter(new FileWriter(file2))
     bw2.write(assertions2.toString)
     //bw2.write(cexSchedule.toString)
     bw2.close()*/

     val model2 = solver.check match {
        case Some(true) => {
            //                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    println("SAT")
            solver.getModel
        }
        case Some(false) => {
            terminate("UNSAT problem")        
        }
      }
      
     // Writing the generated model2 to a file
     val file4 = new File("Model2_10TimeSteps")
     val bw4 = new BufferedWriter(new FileWriter(file4))
     bw4.write(model2.toString)
     bw4.close()

     //Getting the tracked variables to pass as assumptions to get Unsat Core
     val assumptions = (trackScheduleVarsMap.keySet ++ trackAcHypVarsMap.keySet ++ trackLsVarsMap.keySet).toSeq

     //println("Checking Satisfiability with the assumptions") 
     solver.checkAssumptions(assumptions : _*)
     val unsat_core = solver.getUnsatCore().toSeq
     println("Size of Unsat core")
     println(unsat_core.size)

     /*println(trackScheduleVarsMap)
     println(trackAcHypVarsMap)
     println(trackLsVarsMap)*/

     for(uns <- unsat_core)
     {
          if(trackScheduleVarsMap.contains(uns)) {
            val temp = trackScheduleVarsMap(uns)
            val str = temp._1.toString.split("!")(0)
            val v = temp._2
            important_schedule += ((str, v))
          }
          else if(trackAcHypVarsMap.contains(uns)) {
            val temp = trackAcHypVarsMap(uns)
            val str = temp._1.toString.split("!")(0)
            val v = temp._2
            important_achyp += ((str, v))
          } 
          else {
            val temp = trackLsVarsMap(uns)
            val str = temp._1.toString.split("!")(0)
            val v = temp._2.toString
            important_ls += ((str, v))
            }
    }
     
    restartZ3()
    assertExperiments(Settings.runLength, None, None, List(experiment), AssertFateDecision) 
    
    /*
    for(imp <- important_schedule) {
      val astvar = globalMap(imp._1)
      val astval = config2ast(imp._2)
      val toAssert = ctx.mkNot(ctx.mkEq(astvar, astval))
      assertConstraint(toAssert)
     }  

     for(imp <- important_achyp) {
      val astvar = globalMap(imp._1)
      val astval = ctx.mkInt(imp._2, ctx.mkIntSort)
      val toAssert = ctx.mkNot(ctx.mkEq(astvar, astval))
      assertConstraint(toAssert)
     }  
     
     for(imp <- important_ls) {
      val astvar = globalMap(imp._1)
      val value = imp._2
      if(value=="true") {
        val toAssert = ctx.mkNot(ctx.mkEq(astvar, ctx.mkTrue))
        assertConstraint(toAssert)
      } else {
        val toAssert = ctx.mkNot(ctx.mkEq(astvar, ctx.mkFalse))
        assertConstraint(toAssert)
      }*/  
    } 
   }

   /*println("The important SCHEDULE variables are")
   println(important_schedule)
   println("The important AC and HYP variables are")
   println(important_achyp)
   println("The important LS variables are")
   println(important_ls)*/

   println("Number of iterations it took to reach UNSATISFIABLE")
   println(iterCount)
   println("--------------------")
   terminate("Terminated!")
  
  }

  def verify(experiment: Experiment, solution: Solution): Option[CoarseSchedule] = {
    restartZ3()

    assertExperiments(Settings.runLength, None, Some(solution), List(experiment), AssertNegatedFateDecision)

    verificationProfiler.start
    Statistics.solverCalled()
    ctx.checkAndGetModel match {
      case (Some(true), m) => {
        Statistics.solverReturned()
        verificationProfiler.stop
        val cexSchedule = recoverSchedule(m)
        m.delete
        Some(cexSchedule)
      }
      case (Some(false), _) => {
        Statistics.solverReturned()
        verificationProfiler.stop
        None
      }
      case (None, _) => {
        terminate("Solver returned UNKNOWN.")
      }
    }
  }

  def verify(experiments: List[Experiment], solution: Solution): Boolean = {
    var goodSoFar = true
    println("this is the solution being passed in verify method")
    println(solution)
    for (exp <- experiments; if goodSoFar) {
      verify(exp, solution) match {
        case None =>
        case Some(_) => goodSoFar = false
      }
    }
    goodSoFar
  }

  def runSymbolic(experiment: Experiment, schedule: CoarseSchedule, 
      solution: Option[Solution]): Option[(Seq[Cell], History)] = {
    try {
      restartZ3()

      assertExperiments(schedule.size, Some(schedule), solution, List(experiment), AssertNoFateDecision)

      val sanityCheck = true

      // runningProfiler.start
      // ctx.checkAndGetModel match {
      //   case (Some(true), m) => {
      //     runningProfiler.stop

      //     val history = modelMap(m, schedule, experiment)

      //     if (Settings.showGUI)
      //       visualize(history, schedule, experiment)

      //     if (sanityCheck) {
      //       val atMostTwoModels = ctx.checkAndGetAllModels.take(2)
      //       val onlyOneModel = atMostTwoModels.size == 1
      //       if (onlyOneModel)
      //         log("Sanity check for symbolic run: OK")
      //       else {
      //         logError("Sanity check for symbolic run: FAILED")
      //         println("size: " + atMostTwoModels.size)
      //         for ((model, idx) <- atMostTwoModels zipWithIndex)
      //           writeToFile("MODEL" + idx, model.toString)

      //         terminate("sanity check fails")
      //       }
      //     }

      //     Some(history)
      //   }
      //   case _ => {
      //     runningProfiler.stop
      //     logWarning("Run failed for " + experiment)
      //     None
      //   }
      // }

      var counter = 0
      var lastModel: Z3Model = null
      var history: History = null

      Statistics.solverCalled()
      val models = ctx.checkAndGetAllModels.take(1)
      Statistics.solverReturned()

      for (m <- models) {
        counter += 1
        if (counter > 1) {
          logError("Sanity check for symbolic run: FAILED")
          writeToFile("MODEL1", lastModel.toString)
          writeToFile("MODEL2", m.toString)
          terminate("sanity check fails")
        }
          
        lastModel = m
        history = modelMap(m, schedule, experiment)

        //if (Settings.showGUI)
          //visualize(history, schedule, experiment)
      }
      lastModel.delete
      if (counter == 1) {
        Some((schedulesExperimentsCells(schedule)(experiment), history))
      } else {
        logWarning("Run failed for " + experiment)
        None
      }
    } catch {
      case UndefinedHole(id) =>
        logWarning("Hole " + id + " was udefined for " + experiment)
        None
    }
  }

  def decidedFates(cells: Seq[Cell], trace: History): Seq[String] = {
    val maxIndex = trace.keySet.max

    val optionalOutcomes = cells map (decidedFateFromTrace(_, trace, maxIndex))
    optionalOutcomes collect {
      case Some(o) => o
    }
  }

  private def decidedFateFromTrace(cell: Cell, 
      trace: History, finalIndex: Int): Option[String] = {
    def hasOutcome(outcome: String): Boolean = {
      cell.outcomeBundles.get(outcome) match {
        case None => false
        case Some(bundleSet) => {
          bundleSet.foldLeft(false){
            case (acc, bundle) => acc || trace(finalIndex)(bundle.ports(0))
          
          }
        }
      }
    }

    val outcomes = cell.outcomeBundles.keys

    // todo also assert that other outcomes are not decided.
    outcomes.find(hasOutcome(_))
  }
/*
  private def visualize(history: History, schedule: CoarseSchedule, experiment: Experiment) {
    val cells = schedulesExperimentsCells(schedule)(experiment)

    val visualizer = new Visualization.Visualizer()

    for (i <- 0 to schedule.length) {
      for (c <- cells) {
        for (n <- c.N) {
          for (p <- n.P) {
            val modelValue = history(i)(p)
            if (modelValue)
              p.forceEnable()
            else
              p.forceDisable()
          }
        }
      }
      if (i < schedule.length) {
        visualizer.macroSnapshot(cells, schedule(i))
      } else {
        visualizer.macroSnapshot(cells, Nil)
      }
        
    }

    visualizer.show()
  }*/

}