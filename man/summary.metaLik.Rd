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
\code{summary.metaLik} provides summary information about the parameter estimates, standard errors, first- and higher-order log-likelihood ratio statistics. See \code{\link{test.metaLik}} for more details about the first- and higher-order statistics.

}
\value{
The function \code{summary.metaLik} computes and returns a list of information about the fitted \code{metaLik} object, plus
\item{heterogeneity}{maximum likelihood estimate of the between-study heterogeneity parameter \eqn{\tau^2}, its associated standard error and the p-value of the parametric bootstrap score test for heterogeneity.}
\item{fixed effects}{a matrix whose columns are the parameters estimate, the corresponding standard errors, the value of the signed profile log-likelihood ratio statistic (\code{signed logLRT}) for testing the significance of the fixed-effects estimates, the corresponding p-value, the value of the higher-order Skovgaard's (1996) adjustment to \code{signed logLRT}, the corresponding p-value. Higher-order information is supplied only if the bootstrap score test indicates that the maximum likelihood estimate of \eqn{\tau^2} is significantly different from zero. See Guolo (2012) and Guolo and Varin (2012) for details and illustrative examples.}
\item{log-likelihood}{the maximum log-likelihood value.}
}

\references{
Guolo, A. (2012). Higher-Order Likelihood Inference in Meta-Analysis and Meta-Regression. \emph{Statistics in Medicine}, \bold{31}, 313--327.

Guolo, A. and Varin, C. (2012). The R Package metaLik for Likelihood Inference in Meta-Analysis. \emph{Journal of Statistical Software}, \bold{50} (7), 1--14. \url{http://www.jstatsoft.org/v50/i07/}.

Skovgaard, I. M. (1996). An Explicit Large-Deviation Approximation to One-Parameter Tests. \emph{Bernoulli}, \bold{2}, 145--165.
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
## meta-analysis: no evidence of random-effects 
data(albumin)
m <- metaLik(y~1, data=albumin, sigma2=sigma2)
summary(m)
## meta-regression  
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
summary(m)
## meta-regression: no evidence of random-effects
data(cholesterol)
m <- metaLik(heart_disease~chol_reduction, data=cholesterol, weights=1/sigma2)
summary(m)
}
\keyword{regression}
\keyword{htest}
