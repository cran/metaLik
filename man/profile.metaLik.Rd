\name{profile.metaLik}
\alias{profile.metaLik}
\title{
Confidence intervals for a scalar fixed-effect component in meta-analysis and meta-regression models
}
\description{
Computes confidence intervals for a scalar component of the fixed-effects vector in meta-analysis and meta-regression models, using the signed profile log-likelihood ratio test and its second-order Skovgaard's (1996) adjustment.
}
\usage{
\method{profile}{metaLik}(fitted, param=1, level=0.95, display=TRUE, ...)
}
\arguments{
\item{fitted}{an object of class \code{"\link{metaLik}"}.}
\item{param}{a single integer number indicating the parameter associated with the fixed-effects vector component. Default is 1.}
\item{level}{the confidence level required. Default is 0.95.}
\item{display}{logical, whether a graphical representation of the confidence intervals should be diplayed; default is \code{TRUE}.}
\item{...}{additional arguments}
}
\details{
\code{profile.metaLik} computes confidence intervals for a scalar component of interest in the fixed-effects vector. The asymptotic distribution of the first-order statistic and of Skovgaard's (1996) statistic is the standard normal. See \code{\link{test.metaLik}} for more details about the first- and higher-order statistics.
}
\value{
\code{profile.metaLik} returns a matrix with columns the endpoints of the confidence intervals at level \code{level} for the specified parameter according to the signed profile log-likelihood ratio statistic and the Skovgaard's (1996) statistic. In case of \code{display=TRUE}, the confidence intervals are displayed, together with horizontal dashed lines corresponding to the specified confidence level.
}

\references{
Guolo, A. (2011). Higher-order likelihood inference in meta-analysis and meta-regression. \emph{Statistics in Medicine}. Forthcoming.

Skovgaard, I. M. (1996). An explicit large-deviation approximation to one-parameter tests. \emph{Bernoulli}, \bold{2}, 145--165.
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\seealso{
Function \code{\link{metaLik}} for fitting meta-analysis and meta-regression models.

Function \code{\link{test.metaLik}} for hypothesis testing.
}
\examples{
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=vaccine$sigma2)
## significance test for the 'latitude' coefficient
test.metaLik(m, param=2)
## 95% confidence interval for the 'latitude' coefficient
profile(m, param=2)
}
\keyword{regression}
\keyword{htest}
