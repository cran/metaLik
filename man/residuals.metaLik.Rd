\name{residuals.metaLik}
\alias{residuals.metaLik}
\title{
Residuals method for metaLik objects
}
\description{
Extract raw response or Pearson residuals for  \code{"\link{metaLik}"} objects.
}
\usage{
\method{residuals}{metaLik}(object, type=c("pearson", "response", "working"), ...)
}
\arguments{
\item{object}{an object of class "metaLik", usually a result of a call to \code{\link{metaLik}}.}
\item{type}{character indicating type of residuals.}
\item{...}{additional arguments}
}
\details{
Available residuals types are \code{response} or \code{working} for raw residuals, i.e. observed minus fitted values, and \code{pearson} for Pearson residuals.}
\seealso{
\code{\link{metaLik}}
}