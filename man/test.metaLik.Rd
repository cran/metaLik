\name{test.metaLik}
\alias{test.metaLik}
\title{
Hypothesis testing on a scalar fixed-effect component in meta-analysis and meta-regression models
}
\description{
Performs hypothesis testing on a scalar component of the fixed-effects vector in meta-analysis and meta-regression models, using the signed profile log-likelihood ratio test and its higher-order Skovgaard's adjustment (Skovgaard, 1996), as described in Guolo (2012). See Guolo and Varin (2012) for illustrative examples about the usage of \pkg{metaLik} package.
}
\usage{
test.metaLik(object, param=1, value=0, alternative=c("two.sided", "less", "greater"), 
print=TRUE)
}
\arguments{
\item{object}{an object of class \code{"\link{metaLik}"}.}
  \item{param}{a specification of which parameter is to be given confidence interval, either a number or a name. Default is \code{1} corresponding to the intercept.}
\item{value}{a single number indicating the value of the fixed-effect parameter under the null hypothesis. Default is 0.}
\item{alternative}{a character string specifying the alternative hypothesis, must be one of "two.sided" (default), "greater" or "less". Just the initial letter can be specified.}
\item{print}{logical, whether output information should be printed or not; default is \code{TRUE}.}
}
\details{
\code{test.metaLik} allows hypothesis testing on a scalar component of interest in the fixed-effects vector. The signed profile log-likelihood ratio statistic for inference on scalar component \eqn{\beta} of \eqn{\theta} is
    \deqn{
r(\beta) = sign(\hat{\beta}-\beta)\sqrt{2 \{l(\hat{\theta})-l(\theta)\} },}
where \eqn{l} is the log-likelihood function and \eqn{\hat{\theta}} is the maximum likelihood estimate of \eqn{\theta}.
The Skovgaard's adjustment is defined as
  \deqn{
\overline r(\beta) = r(\beta) + \frac{1}{r(\beta)}\log\frac{u(\beta)}{r(\beta)},
}
where \eqn{u(\beta)} is a correction term involving the observed and the expected information matrix and covariances of likelihood quantities, as described in Guolo (2012). Skovgaard's statistic has a second-order accuracy in approximating the standard normal distribution. In the rare case of equal within-study variances, Skovgaard's statistic reaches third-order accuracy.

Higher-order information is supplied only if the Cochran's Q (Cochran, 1937) test indicates for a significant between-study heterogeneity and the monotonicity check is passed, see \code{\link{metaLik}} for details.
}
\value{
A list with the following components:
\item{r}{the value of the signed profile log-likelihood ratio statistic.}
\item{pvalue.r}{the p-value of the signed profile log-likelihood ratio test.}
\item{rskov}{the value of the Skovgaard's statistic.}
\item{pvalue.rskov}{the p-value of the Skovgaard's test.}
\item{check.skov}{logical, whether Q test or monotonicity check are passed. Otherwise (if any or both  the two are not passed),  Skovgaard's statistic is dropped.}
}

\references{
Cochran, W. G. (1937). Problems Arising in the Analysis of a Series of Similar Experiments. \emph{Journal of the Royal Statistical Society Supplement} \bold{4}, 102--118.

Guolo, A. (2012). Higher-Order Likelihood Inference in Meta-Analysis and Meta-Regression. \emph{Statistics in Medicine} \bold{31}, 313--327.

Guolo, A. and Varin, C. (2012). The R Package metaLik for Likelihood Inference in Meta-Analysis. \emph{Journal of Statistical Software} \bold{50} (7), 1--14. \url{http://www.jstatsoft.org/v50/i07/}.

Skovgaard, I. M. (1996). An Explicit Large-Deviation Approximation to One-Parameter Tests. \emph{Bernoulli} \bold{2}, 145--165.
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\seealso{
Function \code{\link{metaLik}} for fitting meta-analysis and meta-regression models.
Function \code{\link{summary.metaLik}} for summaries.
Function \code{\link{profile.metaLik}} for constructing confidence intervals.
}
\examples{
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
## significance test for the intercept coefficient
test.metaLik(m)
## significance test for the 'latitude' coefficient
test.metaLik(m, param=2)
## testing for the 'latitude' coefficient less than 0
test.metaLik(m, param=2, value=0, alternative='less')
}
\keyword{regression}
\keyword{htest}
