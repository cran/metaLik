\name{metaLik}
\alias{metaLik}
\title{
First- and higher-order likelihood inference in meta-analysis and meta-regression models
}
\description{
Implements first-order and higher-order likelihood methods for inference in meta-analysis and meta-regression models, as described in Guolo (2012). Higher-order asymptotics refer to the higher-order adjustment to the log-likelihood ratio statistic for inference on a scalar component of interest as proposed by Skovgaard (1996). See Guolo and Varin (2012) for illustrative examples about the usage of \pkg{metaLik} package. 
}
\usage{
metaLik(formula, data, subset, contrasts = NULL, offset, sigma2, weights=1/sigma2)
}
\arguments{
\item{formula}{an object of class \code{"\link{formula}"} (or one that
    can be coerced to that class): a symbolic description of the
    model to be fitted.  The details of model specification are given
    under \sQuote{Details}.}
  \item{data}{an optional data frame, list or environment (or object
    coercible by \code{\link{as.data.frame}} to a data frame) containing
    the variables in the model.  If not found in \code{data}, the
    variables are taken from \code{environment(formula)}, typically the environment from which \code{metaLik} is called.}
\item{subset}{an optional vector specifying a subset of observations to be used in the fitting process.}
\item{contrasts}{an optional list. See the contrasts.arg of \code{\link{model.matrix.default}}.}
\item{offset}{this can be used to specify an a priori known component to be included in the linear predictor during fitting. This should be \code{NULL} or a numeric vector of length equal to the number of cases. One or more \code{\link{offset}} terms can be included in the formula instead or as well, and if more than one are specified their sum is used. See \code{\link{model.offset}}.}
\item{sigma2}{a vector of within-study estimated variances. The length of the vector must be the same of the number of studies.}
\item{weights}{a vector of the inverse of within-study estimated variances. The length of the vector must be the same of the number of studies. If \code{sigma2} is supplied, the value of \code{weights} is discarded.}
}
\details{
Models for \code{metaLik.fit} are specified simbolically. A typical model has the form \code{y ~ x1 + \ldots + xJ}, where \code{y} is the continuous response term and \code{xj} is the j-th covariate available at the aggregated meta-analysis level for each study. The case of no covariates corresponds to the classical meta-analysis model specified as \code{y~1}.

Within-study variances are specified through \code{sigma2}: the rare case of equal within-study variances implies Skovgaard's adjustment reaching a third-order accuracy. 

DerSimonian and Laird estimates (DerSimonian and Laird, 1986) are also supplied. 
}
\value{
An object of class \code{"metaLik"} with the following components:
\item{y}{the y vector used.}
\item{X}{the model matrix used.}
\item{fitted.values}{the fitted values.}
\item{sigma2}{the within-study variances used.}
\item{K}{the number of studies.}
\item{mle}{the vector of the maximum likelihood parameter estimates.}
\item{vcov}{the variance-covariance matrix of the parameter estimates.}
\item{max.lik}{the maximum log-likelihood value.}
\item{beta.mle}{the vector of fixed-effects parameters estimated according to maximum likelihood.}
\item{tau2.mle}{the maximum likelihood estimate of \eqn{\tau^2}.}
\item{DL}{the vector of fixed-effects parameters estimated according to DerSimonian and Laird's pproach.}
\item{tau2.DL}{the method of moments estimate of the heterogeneity parameter \eqn{\tau^2}.}
\item{vcov.DL}{the variance-covariance matrix of the DL parameter estimates.}
\item{call}{the matched call.}
\item{formula}{the \code{\link{formula}} used.}
\item{terms}{the \code{\link{terms}} object used.}
\item{offset}{the offset used.}
\item{contrasts}{(only where relevant) the \code{\link{contrasts}} specified.}
\item{xlevels}{(only where relevant) a record of the levels of the factors used in fitting.}
\item{model}{the model frame used.}
Generic functions \code{\link{coefficients}}, \code{\link{vcov}}, \code{\link{logLik}}, \code{\link{fitted}}, \code{\link{residuals}} can be used to extract fitted model quantities. 
}
\references{ 
DerSimonian, R. and Laird, N. (1986). Meta-Analysis in Clinical Trials. \emph{Controlled Clinical Trials} \bold{7}, 177--188.

Guolo, A. (2012). Higher-Order Likelihood Inference in Meta-Analysis and Meta-Regression. \emph{Statistics in Medicine} \bold{31}, 313--327.

Guolo, A. and Varin, C. (2012). The R Package metaLik for Likelihood Inference in Meta-Analysis. \emph{Journal of Statistical Software} \bold{50} (7), 1--14. \url{http://www.jstatsoft.org/v50/i07/}.

Skovgaard, I. M. (1996). An Explicit Large-Deviation Approximation to One-Parameter Tests. \emph{Bernoulli} \bold{2}, 145--165.
}
\author{
Annamaria Guolo and Cristiano Varin.
}
\seealso{
Function \code{\link{summary.metaLik}} for summaries.

Function \code{\link{test.metaLik}} for hypothesis testing.
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
