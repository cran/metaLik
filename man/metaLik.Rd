\name{metaLik}
\alias{metaLik}
\title{
First- and higher-order likelihood inference in meta-analysis and meta-regression models
}
\description{
Implements first-order and higher-order likelihood methods for inference in meta-analysis and meta-regression models, as described in Guolo (2011). Higher-order asymptotics refer to the second-order adjustment to the log-likelihood ratio statistic for inference on a scalar component of interest as proposed by Skovgaard (1996).
}
\usage{
metaLik(formula, data, subset, contrasts = NULL, offset, sigma2)
}
\arguments{
\item{formula}{an object of class \code{"\link{formula}"} (or one that
    can be coerced to that class): a symbolic description of the
    model to be fitted.  The details of model specification are given
    under \sQuote{Details}.}
  \item{data}{an optional data frame, list or environment (or object
    coercible by \code{\link{as.data.frame}} to a data frame) containing
    the variables in the model.  If not found in \code{data}, the
    variables are taken from \code{environment(formula)},
    typically the environment from which \code{lm} is called.}
\item{subset}{an optional vector specifying a subset of observations to be used in the fitting process.}
\item{contrasts}{an optional list. See the contrasts.arg of \code{\link{model.matrix.default}}.}
\item{offset}{this can be used to specify an a priori known component to be included in the linear predictor during fitting. This should be \code{NULL} or a numeric vector of length equal to the number of cases. One or more \code{\link{offset}} terms can be included in the formula instead or as well, and if more than one are specified their sum is used. See \code{\link{model.offset}}.}
\item{sigma2}{a vector of within-study estimated variances. The length of the vector must be the same of the number of studies.}
}
\details{
Models for \code{metaLik.fit} are specified simbolically. A typical model has the form \code{y ~ x1 + x2 + \ldots + xJ}, where \code{y} is the continuous response term and \code{xj} is the j-th covariate available at the aggregated meta-analysis level for each study, \code{j, 1, \ldots, p}. The case of no \code{xj} corresponds to the classical meta-analysis model. Within-study variances are specified through \code{sigma2}: the rare case of equal within-study variances implies Skovgaard's adjustment reaching a third-order accuracy. The fixed-effects estimate through DerSimonian and Laird's (1986) approach is also supplied. In this case, the method of moments estimator of the heterogeneity parameter \eqn{\tau^2} is considered. 
}
\value{
An object of class \code{"metaLik"} with the following components:
\item{mle}{the vector of the parameter estimates.}
\item{vcov}{the variance-covariance matrix of the parameter estimates.}
\item{max.lik}{the maximum log-likelihood value.}
\item{DL}{the vector of fixed-effects parameters estimated according to DerSimonian and Laird's (1986) approach.}
\item{tau2.DL}{the method of moments estimate of the heterogeneity parameter \eqn{\tau^2}.}
\item{vcov.DL}{thet variance-covariance matrix of the DL parameter estimates.}
\item{K}{number of studies.}
\item{y}{the y vector used.}
\item{X}{the model matrix used.}
\item{offset}{the offset used.}
\item{sigma2}{the within-study variances used.}
\item{call}{the matched call.}
Functions \code{\link{coefficients}}, \code{\link{vcov}} can be used to extract estimated model parameters and their variance-covariance matrix.
}
\references{
DerSimonian, R. and Laird, N. (1986). Meta-analysis in clinical trials. \emph{Controlled Clinical Trials}, \bold{7}, 177--188.

Skovgaard, I. M. (1996). An explicit large-deviation approximation to one-parameter tests. \emph{Bernoulli}, \bold{2}, 145--165.

Guolo, A. (2011). Higher-order likelihood inference in meta-analysis and meta-regression. \emph{Statistics in Medicine}. Forthcoming. 
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\seealso{
Function \code{\link{summary.metaLik}} for summaries.

The generic functions \code{\link{coef}}, \code{\link{confint}}, \code{\link{vcov}}, \code{\link{model.matrix}}, \code{\link{model.frame}}, \code{\link{logLik}}, and \code{\link{residuals}}. 

Function \code{\link{test.metaLik}} for hypothesis testing.

Function \code{\link{profile.metaLik}} for constructing confidence intervals.
}
\examples{
data(vaccine)
m <- metaLik(y~latitude, data=vaccine, sigma2=vaccine$sigma2)
summary(m)
}
\keyword{regression}
\keyword{htest}
