\name{cholesterol}
\alias{cholesterol}
\docType{data}
\title{
Serum cholesterol data.  
}
\description{
Data from 28 randomized trials about the effect of serum cholesterol reduction on the risk of ischaemic heart disease.
}
\usage{data(cholesterol)}
\format{
\describe{
\item{\code{heart_disease}}{log odds ratio of ischaemic heart disease.}
\item{\code{chol_reduction}}{average serum cholesterol reduction measured in mmol/l.}
\item{\code{sigma2}}{estimated within-study variance.}
}
}
\source{
Law, M.R., Wald, N.J. and Thmpson, S.G. (1994). By how much and how quickly does reduction in serum cholesterol concentration lower risk of ischaemic heart disease? \emph{British Medical Journal} \bold{308}, 367--373.

Thompson, S.G. and Sharp, S.J. (1999). Explaining heterogeneity in meta-analysis: a comparison of methods. \emph{Statistics in Medicine} \bold{18}, 2693--2708.
}
\examples{
data(cholesterol)
}
\keyword{datasets}