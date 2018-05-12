package elegans

import Cells._
import Constraints._
import Experiments._
import Invariants._

import scala.util.Random

object ScheduleSummarization {

	def summarizeSchedule(e : Experiment, solution : Option[Solution]) = {
		synthesizeSchedule(e, solution) match {
			case Some(sch) => 
				println("The generated schedule is:")
				println(sch)
			case None => 
		}
	}

	def summarizeSchedules(experiments : Seq[Experiment], 
		solution : Option[Solution]) = {
		for (e <- experiments) {
			summarizeSchedule(e, solution)
			}
		}

}