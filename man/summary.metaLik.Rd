\name{summary.metaLik}
\alias{summary.metaLik}
\title{
Summarizing meta-analysis and meta-regression model fits
}
\description{
Summary method for class \code{"\link{metaLik}"}. 
}
\usage{
\method{summary}{metaLik}(object, ...)
}
\arguments{
\item{object}{an object of class "metaLik", usually a result of a call to \code{"\link{metaLik}"}.}
\item{...}{additional arguments}
}
\details{
\code{summary.metaLik} prints summary information about within-study heterogeneity, parameter estimates, standard errors, first- and higher-order log-likelihood ratio statistics. See \code{\link{test.metaLik}} for more details about the first- and higher-order statistics.
}
\value{
The function \code{summary.metaLik} returns the \code{metaLik} object from which \code{summary.metaLik} is called.
}


\seealso{

The generic functions \code{\link{coefficients}}, \code{\link{confint}} and \code{\link{vcov}}. 

Function \code{\link{test.metaLik}} allows for hypothesis testing.
}
\examples{
## meta-analysis
data(education)
m <- metaLik(y~1, data=education, sigma2=sigma2)
summary(m)
## meta-analysis
data(albumin)
m <- metaLik(y~1, data=albumin, sigma2=sigma2)
summary(m)
## meta-regression  
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
summary(m)
## meta-regression
data(cholesterol)
m <- metaLik(heart_disease~chol_reduction, data=cholesterol, weights=1/sigma2)
summary(m)
}
\keyword{regression}
\keyword{htest}
