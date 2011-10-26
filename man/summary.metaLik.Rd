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
\item{object}{an object of class "metaLik", usually, a result of a call to \code{"\link{metaLik}"}.}
\item{...}{additional arguments}
}
\details{
\code{summary.metaLik} provides summary information about the parameter estimates, standard errors, information about first- and higher-order log-likelihood ratio statistics. See \code{\link{test.metaLik}} for more details about the first- and higher-order statistics.

}
\value{
The function \code{summary.metaLik} computes and returns a list of informations of the fitted \code{metaLik} model given in object, using the component "call" from its argument, plus
\item{heterogeneity}{estimate of the between-study heterogeneity parameter \eqn{\tau^2} and its associated standard error.}
\item{fixed effects}{a \eqn{p x 6} matrix, with columns for the parameter estimate, its corresponding standard error, the value of the signed profile log-likelihood ratio statistic (\code{signed logLRT}) for testing the significance of the parameter, the corresponding p-value, the value of the second-order Skovgaard's (1996) adjustment to \code{signed logLRT}, the corresponding p-value.}
\item{log-likelihood}{the maximum log-likelihood value.}
}

\references{
Guolo, A. (2011). Higher-order likelihood inference in meta-analysis and meta-regression. \emph{Statistics in Medicine}. Forthcoming.

Skovgaard, I. M. (1996). An explicit large-deviation approximation to one-parameter tests. \emph{Bernoulli}, \bold{2}, 145--165.
}

\seealso{

The generic functions \code{\link{coefficients}}, \code{\link{confint}} and \code{\link{vcov}}. 

Function \code{\link{test.metaLik}} allows for hypothesis testing.
}
\examples{
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=vaccine$sigma2)
summary(m)
}
\keyword{regression}
\keyword{htest}
