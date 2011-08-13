\name{vaccine}
\alias{vaccine}
\docType{data}
\title{
Data for Bacillus Calmette-Guerin (BCG) vaccine studies.  
}
\description{
Data from 13 clinical studies evaluating the efficacy of the BCG vaccine for the prevention of tuberculosis.   
}
\usage{data(vaccine)}
\format{
\describe{
\item{\code{y}}{logarithm of the risk ratio in each study.}
\item{\code{latitude}}{latitude, distance of each study from the equator, surrogate for the presence of environmental mycobacteria providing a level of natural immunity against tuberculosis.}
\item{\code{year}}{year of the study.}
\item{\code{sigma2}}{estimated within-study variance.}
}
}
\source{
Berkey, C.S., Hoaglin, D.C., Mosteller, F. and Colditz, G.A. (1995). A random-effects regression model for meta-analysis. \emph{Statistics in Medicine} \bold{14}, 395--411.
}
\examples{
data(vaccine)
}
\keyword{datasets}