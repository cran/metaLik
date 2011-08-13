\name{test.metaLik}
\alias{test.metaLik}
\title{
Hypothesis testing on a scalar fixed-effect component in meta-analysis and meta-regression models
}
\description{
Performs hypothesis testing on a scalar component of the fixed-effects vector in meta-analysis and meta-regression models, using the signed profile log-likelihood ratio test and its second-order Skovgaard's adjustment.
}
\usage{
test.metaLik(object, param=1, value=0, alternative=c("two.sided", 
"less", "greater"), print=TRUE)
}
\arguments{
\item{object}{an object of class \code{"\link{metaLik}"}.}
  \item{param}{a single integer number indicating the parameter associated with the fixed-effects vector component. Default is 1.}
\item{value}{a single number indicating the value of the fixed-effect parameter under the null hypothesis. Default is 0.}
\item{alternative}{a character string specifying the alternative hypothesis, must be one of "two.sided" (default), "greater" or "less". Just the initial letter can be specified.}
\item{print}{logical, whether output information should be printed or not; default is \code{TRUE}.}
}
\details{
\code{test.metaLik} allows hypothesis testing on a scalar component of interest in the fixed-effects vector. The asymptotic distribution of the evaluated statistics is the standard normal. 
Let \eqn{\theta} be the whole parameter vector. The signed profile log-likelihood ratio statistic for inference on scalar component \eqn{\beta} of \eqn{\theta} is
    \deqn{
r(\beta) = sign(\hat{\beta}-\beta)\sqrt{2 \{l(\hat{\theta})-l(\theta)\} },}
where \eqn{l()} is the log-likelihood function and \eqn{\hat{\theta}} is the maximum likelihood estimate of \eqn{\theta}.
The Skovgaard's (1996) second-order adjustment is defined as
  \deqn{
\overline r(\beta) = r(\beta) + \frac{1}{r(\beta)}\log\frac{u(\beta)}{r(\beta)},
}
where \eqn{u(\beta)} is a correction term involving the observed and the expected information matrix and covariances of likelihood quantities, as described in Guolo (2011).
}
\value{
A list with the following components:
\item{First-order statistic}{the value of the signed profile log-likelihood ratio statistic and the associated p-value of the test.}
\item{Skovgaard's statistic}{the value of the Skovgaard's statistic and the associated p-value of the test.}
\item{alternative}{a character string describing the alternative hypothesis.}
}

\references{
Skovgaard, I. M. (1996). An explicit large-deviation approximation to one-parameter tests. \emph{Bernoulli}, \bold{2}, 145--165.

Guolo, A. (2011). Higher-order likelihood inference in meta-analysis and meta-regression. Preprint. 
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
m <- metaLik(y~latitude, data=vaccine, sigma2=vaccine$sigma2)
print(m)
## significance test for the intercept coefficient
test.metaLik(m)
## significance test for the 'latitude' coefficient
test.metaLik(m, param=2)
## testing for the 'latitude' coefficient less than 0
test.metaLik(m, param=2, value=0, alternative='less')
}
\keyword{regression}
\keyword{htest}
