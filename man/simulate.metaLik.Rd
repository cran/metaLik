\name{simulate.metaLik}
\alias{simulate.metaLik}
\title{
Simulate meta-analysis outcomes
}
\description{
Simulate one or more meta-analysis outcomes from a fitted \code{\link{metaLik}} object.
}
\usage{
\method{simulate}{metaLik}(object, nsim=1, seed=NULL, ...)
}
\arguments{
\item{object}{an object of class \code{"\link{metaLik}"}.}
\item{nsim}{number of outcome vectors to simulate. Default is \code{1}.}
\item{seed}{an object specifying if and how the random number generator should be initialized, see \code{\link{simulate}} for details.}
\item{...}{additional optional arguments.}
}
\value{
A dataframe containing the simulated meta-analysis outcomes. 
}
\references{
DerSimonian, R. and Laird, N. (1986). Meta-Analysis in Clinical Trials. \emph{Controlled Clinical Trials} \bold{7}, 177--188.
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\examples{
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
sim <- simulate(m, nsim=2)
sim
}
\keyword{regression}
\keyword{models}