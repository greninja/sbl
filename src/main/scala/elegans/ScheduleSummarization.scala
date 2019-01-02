package elegans

import Cells._
import Constraints._
import Experiments._
import Invariants._

import scala.util.Random

import z3.scala._

object ScheduleSummarization {

	private var ctx_ : Z3Context = null 
	def ctx = ctx_

	def summarizeSchedule(e : Experiment, solution : Option[Solution]) = {
		
		/*
		synthesizeSchedule(e, solution) match {
			case ctx => 
				println("The generated ctx is:")
				println(ctx)
			//case None => 
		}*/
		
		synthesizeSchedule(e, solution)
	}

	def summarizeSchedules(experiments : Seq[Experiment], solution : Option[Solution]) = {
		for (e <- experiments) {
			summarizeSchedule(e, solution)
			}
		}
}