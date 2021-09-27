package org.atlanmod.findcouples.model.movie.element

import org.atlanmod.findcouples.model.movie.MovieMetamodel

class MovieCouple extends MovieGroup (MovieMetamodel.COUPLE) {

    def this(id: String, avgRating: Double) = {
        this()
        super.eSetProperty("avgRating", avgRating)
        super.eSetProperty("id", id)
    }

    override def getId: String = super.eGetProperty("id").asInstanceOf[String]
    override def getAvgRating: Double = super.eGetProperty("avgRating").asInstanceOf[Double]

    override def toString: String = "Couple (" + getAvgRating + ")"

    override def equals(o: Any): Boolean = {
        o match {
            case obj: MovieCouple =>
                this.getId.equals(obj.getId) & this.getAvgRating.equals(obj.getAvgRating)
            case _ => false
        }
}

    override def weak_equals(o: Any): Boolean = equals(o)


}
