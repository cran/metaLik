\name{profile.metaLik}
\alias{profile.metaLik}
\title{
Confidence intervals for a scalar fixed-effect component in meta-analysis and meta-regression models
}
\description{
Computes confidence intervals for a scalar component of the fixed-effects vector in meta-analysis and meta-regression models, using the signed profile log-likelihood ratio test and its higher-order Skovgaard's (1996) adjustment, as described in Guolo (2012). See Guolo and Varin (2012) for illustrative examples about the usage of \pkg{metaLik} package.
}
\usage{
\method{profile}{metaLik}(fitted, param=1, level=0.95, display=TRUE, ...)
}
\arguments{
\item{fitted}{an object of class \code{"\link{metaLik}"}.}
\item{param}{a specification of which parameter is to be given confidence interval, either a number or a name. Default is \code{1} corresponding to the intercept.}
\item{level}{the confidence level required. Default is 0.95.}
\item{display}{logical, whether a graphical representation of the confidence intervals should be diplayed; default is \code{TRUE}.}
\item{...}{additional arguments}
}
\details{
\code{profile.metaLik} computes confidence intervals for a scalar component of interest in the fixed-effects vector. See \code{\link{test.metaLik}} for more details about the first- and higher-order statistics.
}
\value{
\code{profile.metaLik} returns a matrix with columns the endpoints of the confidence intervals at level \code{level} for the specified parameter according to the signed profile log-likelihood ratio statistic and the Skovgaard's (1996) statistic. In case of \code{display=TRUE}, the signed square root of the profile likelihood is plotted together with the horizontal dashed lines relative to the specified \code{level} and the corresponding confidence intervals. The package checks whether the maximum likelihood estimate of \eqn{\tau^2} is not significant (see \code{\link{metaLik}} for details): in this case, the random-effect is dropped and Skovgaard's correction vanishes.
}

\references{
Guolo, A. (2012). Higher-Order Likelihood Inference in Meta-Analysis and Meta-Regression. \emph{Statistics in Medicine}, \bold{31}, 313--327.

Guolo, A. and Varin, C. (2012). The R Package metaLik for Likelihood Inference in Meta-Analysis. \emph{Journal of Statistical Software}, \bold{50} (7), 1--14. \url{http://www.jstatsoft.org/v50/i07/}.

Skovgaard, I. M. (1996). An Explicit Large-Deviation Approximation to One-Parameter Tests. \emph{Bernoulli}, \bold{2}, 145--165.
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\seealso{
Function \code{\link{metaLik}} for fitting meta-analysis and meta-regression models.

Function \code{\link{test.metaLik}} for hypothesis testing.
}
\examples{
## meta-regression
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=sigma2)
## significance test for the 'latitude' coefficient
test.metaLik(m, param=2)
## 95% confidence interval for the 'latitude' coefficient
profile(m, param="latitude")
## meta-regression
data(cholesterol)
m <- metaLik(heart_disease~chol_reduction, data=cholesterol, weights=1/sigma2)
## no evidence of random-effects
## significance test for the 'chol_reduction' coefficient
test.metaLik(m, param=2)
## 95% confidence interval for the 'chol_reduction' coefficient
profile(m, param="chol_reduction")
}
\keyword{regression}
\keyword{htest}
