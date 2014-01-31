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
The function \code{summary.metaLik} computes and returns a list of information about the fitted \code{metaLik} object including
\item{heterogeneity}{maximum likelihood estimate of the between-study heterogeneity parameter \eqn{\tau^2}, the Cochran's Q test (Cochran, 1937) for between-study heterogeneity and the associated p-value.}
\item{fixed effects}{a matrix whose columns are the parameters estimate, the corresponding standard errors, the value of the signed profile log-likelihood ratio statistic (\code{signed logLRT}) for testing the significance of the fixed-effects estimates, the corresponding p-value, the value of the higher-order Skovgaard's adjustment to \code{signed logLRT} (Skovgaard, 1996), the corresponding p-value. See Guolo (2012) and Guolo and Varin (2012) for details and illustrative examples. Higher-order information is supplied only if the Cochran's Q test concludes for a significant between-study heterogeneity.}
\item{log-likelihood}{the maximum log-likelihood value.}
}

\references{
Cochran, W. G. (1937). Problems Arising in the Analysis of a Series of Similar Experiments. \emph{Journal of the Royal Statistical Society Supplement} \bold{4}, 102--118.

Guolo, A. (2012). Higher-Order Likelihood Inference in Meta-Analysis and Meta-Regression. \emph{Statistics in Medicine} \bold{31}, 313--327.

Guolo, A. and Varin, C. (2012). The R Package metaLik for Likelihood Inference in Meta-Analysis. \emph{Journal of Statistical Software} \bold{50} (7), 1--14. \url{http://www.jstatsoft.org/v50/i07/}.

Skovgaard, I. M. (1996). An Explicit Large-Deviation Approximation to One-Parameter Tests. \emph{Bernoulli} \bold{2}, 145--165.
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
## meta-analysis: no significant between-study heterogeneity
data(albumin)
m <- metaLik(y~1, data=albumin, sigma2=sigma2)
summary(m)
## meta-regression  
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
summary(m)
## meta-regression: no significant between-study heterogeneity
data(cholesterol)
m <- metaLik(heart_disease~chol_reduction, data=cholesterol, weights=1/sigma2)
summary(m)
}
\keyword{regression}
\keyword{htest}
