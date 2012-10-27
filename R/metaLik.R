.likTerms <- function(y, X, sigma2){

  ntheta <- NCOL(X)+1
  ans <- list()
  
  ans$lik <- function(theta, fixed=rep(NA, ntheta)){
    
    all.theta <- fixed
    all.theta[is.na(fixed)] <- theta
    beta <- all.theta[-ntheta]
    tau2 <- all.theta[ntheta]
    v <- tau2+sigma2
    if(tau2<0)
      return(NA)
    res <- y-X%*%beta      
    -0.5*sum(log(v))-0.5*t(res)%*%diag(1/v)%*%res 
  }
  ans$glik <- function(theta, fixed=rep(NA, ntheta)){
    
    grad <- double(ntheta)
    all.theta <- fixed
    all.theta[is.na(fixed)] <- theta
    beta <- all.theta[-ntheta]
    tau2 <- all.theta[ntheta]
    v <- tau2+sigma2
    res <- y-X%*%beta 
    grad[1:(ntheta-1)] <- t(res)%*%diag(1/v)%*%X
    grad[ntheta] <- .5*( t(res)%*%diag(1/v^2)%*%res-sum(1/v) )
    
    grad[is.na(fixed)]
    
  }
  ans$Jmatrix <- function(theta){
    
    beta <- matrix(theta[-ntheta], ncol=1)
    tau2 <- theta[ntheta]
    Info <- matrix(0, ncol=ntheta, nrow=ntheta)
    v <- tau2+(sigma2)
    res <- y-X%*%beta
    Info[1:(ntheta-1), 1:(ntheta-1)] <- t(X)%*%diag(1/v)%*%(X)
    Info[1:(ntheta-1), ntheta] <- t(X)%*%diag(1/v^2)%*%res
    Info[ntheta, 1:(ntheta-1)] <- Info[1:(ntheta-1), ntheta]
    Info[ntheta, ntheta] <- -0.5*sum(1/v^2)+t(res)%*%diag(1/v^3)%*%res    
    
    Info
  }
  ans$Imatrix <- function(theta){
      
    tau2 <- theta[ntheta]
    Info <- matrix(0, ncol=ntheta, nrow=ntheta)
    v <- tau2+sigma2
    Info[1:(ntheta-1), 1:(ntheta-1)] <- t(X)%*%diag(1/v)%*%X
    Info[ntheta, ntheta] <- 0.5*sum(1/v^2)
    
    Info
  }
  ans$Smatrix <- function(theta.mle, theta.constr){
    
    beta.mle <- matrix(theta.mle[-ntheta], ncol=1)
    beta.constr <- matrix(theta.constr[-ntheta], ncol=1)
    tau2 <- theta.constr[ntheta]
    S <- matrix(0, ncol=ntheta, nrow=ntheta)
    v <- tau2+sigma2
    S[1:(ntheta-1), 1:(ntheta-1)] <- t(X)%*%diag(1/v)%*%X
    S[1:(ntheta-1), ntheta] <- t(X)%*%diag(1/v^2)%*%X%*%(beta.mle-beta.constr)
    S[ntheta, ntheta] <- 0.5*sum(1/v^2)
    
    S
  }
  ans$qvect <- function(theta.mle, theta.constr){
    
    beta.mle <- matrix(theta.mle[-ntheta], ncol=1)
    beta.constr <- matrix(theta.constr[-ntheta], ncol=1)
    tau2.mle <- theta.mle[ntheta]
    tau2.constr <- theta.constr[ntheta]
    qvect <- rep(0.0, ntheta)
    v.mle <- tau2.mle+sigma2
    v.constr <- tau2.constr+sigma2
    qvect[1:(ntheta-1)] <- t(X)%*%diag(1/v.constr)%*%(X)%*%(beta.mle-beta.constr)
    qvect[ntheta] <- -0.5*sum(1/v.mle-1/v.constr)
    
    qvect
  }
  class(ans) <- c("lik.metaLik")
  ans
}

metaLik <- function(formula, data, subset, contrasts = NULL, offset, sigma2, weights=1/sigma2){

  call <- match.call()
  if (missing(data)) 
    data <- environment(formula)
  mf <- match.call(expand.dots = FALSE)
  m <- match(c("formula", "data", "subset", "offset", "sigma2", "weights"), names(mf), 0L)
  mf <- mf[c(1L, m)]
  mf$drop.unused.levels <- TRUE
  mf[[1L]] <- as.name("model.frame")
  mf <- eval(mf, parent.frame())
  mt <- attr(mf, "terms")
  y <- model.response(mf, "any")
  sigma2 <- model.extract(mf, sigma2)
  if(is.null(sigma2)){
    w <- model.extract(mf, weights)
    if(is.null(w))
      stop("metaLik requires within-studies variances specified either by sigma2 or by weights\n")
    sigma2 <- 1/w
  }
  if (is.empty.model(mt)) 
    stop("metaLik requires model specification\n")
  X <- model.matrix(mt, mf, contrasts)
  offset <- as.vector(model.offset(mf))
  if (!is.null(offset)) {
    if (length(offset) != length(y)) 
      stop(gettextf("number of offsets is %d should equal %d (number of observations)", 
                    length(offset), length(y)), domain = NA)
  }
  if (is.null(offset)) 
    offset <- rep.int(0, length(y))
  y <- y-offset
  
  lik <- .likTerms(y, X, sigma2)$lik
  glik <- .likTerms(y, X, sigma2)$glik
  Jmatrix <- .likTerms(y, X, sigma2)$Jmatrix
        
  ## compute DL estimates
  D <- diag(sigma2, ncol=NROW(X), nrow=NROW(X))
  P <- diag(NROW(X)) - X%*%solve(t(X)%*%solve(D)%*%X)%*%t(X)%*%solve(D)
  q.stat <- t(y)%*%t(P)%*%solve(D)%*%P%*%y
  t.value <- (q.stat-NROW(X)+NCOL(X))/(sum(diag(solve(D)))-sum(diag( solve(t(X)%*%solve(D)%*%X)%*%t(X)%*%solve(D)^2%*%X )))
  tau2.dl <- max(0, t.value)
  weights.dl <- diag(tau2.dl, ncol=NROW(X), nrow=NROW(X)) + D
  beta.dl <- solve(t(X)%*%solve(weights.dl)%*%X)%*%t(X)%*%solve(weights.dl)%*%y
  var.dl <- solve(t(X)%*%solve(weights.dl)%*%X)
  
  ## compute MLE
  start.theta <- c(beta.dl, var(y))
  ntheta <- length(start.theta)
  op <- optim(start.theta, fn=lik, gr=glik, method="BFGS", control=list(fnscale=-1, maxit=500))
  if(op$convergence)
    stop("optim: convergence not reached.\n")
  theta.mle <- op$par
  ntheta <- length(theta.mle)
  
  ## parametric bootstrap test of homogeneity
  fit.fe <- lm(y~0+X, weights=1/sigma2)
  nboot <- 1000
  boot.sim <- replicate( nboot, rnorm(length(y), fitted(fit.fe), sqrt(sigma2)) )
  score.stat <- function(this.y, observed=FALSE){
    this.fit <- lm.wfit(x=X, y=this.y, w=1/sigma2)
    this.theta <- c(coef(this.fit), 0.0)
    g <- .likTerms(this.y, X, sigma2)$glik(this.theta)
    if(!observed){
      I <- .likTerms(this.y, X, sigma2)$Imatrix(this.theta)
      return( g[ntheta]^2/I[ntheta,ntheta] )
    }
    else{
      J <- .likTerms(this.y, X, sigma2)$Jmatrix(this.theta)
      return( g[ntheta]^2/(J[ntheta,ntheta]-J[ntheta,-ntheta]%*%solve(J[-ntheta,-ntheta])%*%J[-ntheta,ntheta]) )
    }
  }
  obs.score <- score.stat(y)
  boot.scores <- apply(boot.sim, 2, score.stat)
  pval.tau2 <- mean( boot.scores>obs.score )
  
  if(pval.tau2<0.05){
    vcov.mle <- try( solve(Jmatrix(theta.mle)) )
    if(inherits(vcov.mle, "try-error") || any(diag(vcov.mle)<0))
      stop("convergence not reached, perhaps too few studies.\n")
  }
  else{
    theta.mle <- c( coef(fit.fe), 0.0)
    vcov.mle <- matrix(0.0, nrow=ntheta, ncol=ntheta)
    vcov.mle[-ntheta,-ntheta] <- vcov(fit.fe)
  }
  names(theta.mle) <- colnames(vcov.mle) <- rownames(vcov.mle) <- c(colnames(X), "tau^2")
  fitted.values <- X%*%theta.mle[-ntheta]
    
  ## exit
  m <- structure(list(y=y+offset, X=X, fitted.values=fitted.values, sigma2=sigma2, K=NROW(X), mle=theta.mle, vcov=vcov.mle, max.lik=lik(theta.mle), tau2.mle=op$par[ntheta], pval.tau2=pval.tau2, DL=beta.dl, tau2.DL=tau2.dl, vcov.DL=var.dl, call=call, formula=formula, terms=mt,  offset=offset, contrasts = attr(X, "contrasts"), xlevels = .getXlevels(mt, mf), model=mf), class="metaLik")
  m
}

print.metaLik <- function(x, digits = max(3, getOption("digits") - 3), ...) 
{
  cat("\nCall:\n",
      paste(deparse(x$call), sep="\n", collapse = "\n"), "\n\n", sep="")
  if(length(coef(x))) {
    cat("Coefficients:\n")
    print.default(format(coef(x), digits=digits),
                  print.gap = 2, quote = FALSE)
  } else cat("No coefficients\n")
  cat("\n")
  cat("Variance/covariance matrix:\n")
  print.default(format(vcov(x), digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("Maximum likelihood estimate of tau^2:\n")
  print.default(format(x$tau2.mle, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("Score test for homogeneity p-value:\n")
  print.default(format(x$pval.tau2, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("Maximized log-likelihood:\n")
  print.default(format(as.numeric(x$max.lik), digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("DL coefficients:\n")
  print.default(format(x$DL, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("DL Variance/covariance matrix:\n")
  print.default(format(x$vcov.DL, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("DL tau^2 estimate:\n")
  print.default(format(x$tau2.DL, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("Number of studies K:\n")
  print.default(x$K)
  cat("\n")
  cat("y:\n")
  print.default(format(x$y, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("X:\n")
  print.default(format(x$X, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("offset:\n")
  print.default(format(x$offset, digits=digits),
                print.gap = 2, quote = FALSE)
  cat("\n")
  cat("Within-study variances:\n")
  print.default(format(x$sigma2, digits=digits),
                print.gap = 2, quote = FALSE)
  invisible(x)
}

test.metaLik <- function(object, param=1, value=0, alternative=c("two.sided", "less", "greater"), print=TRUE){

  digits <- max(3, getOption("digits") - 3)
  if(class(object)!="metaLik")
    stop("\nfunction designed for 'metaLik' objects")
  if(is.character(param)){
    pnames <- names(coef(object))
    param <- match(param, pnames, nomatch=NA)
  }
  if(missing(param) || is.na(param)){
    param <- 1L
    warning("\nassumed confidence interval for intercept")
  }   
  if(length(param)>1 || param>length(coef(object)) || param<=0 || !is.numeric(param))
    stop("\n'param' must be one single fixed-effects component")
  alternative <- match.arg(alternative)
  if(!missing(value) && (length(value)!= 1 || is.na(value)))
    stop("\n'value' must be a single number")
  if(class(object)!="metaLik")
    stop("\n'object' must be a metaLik object")
   
  pl <- .profLik(object, param=param)
  values <- pl$values
  rs <- pl$rs
  us <- pl$us
  rtheta <- predict(smooth.spline(values, rs), x=value)$y
  theta.mle <- object$mle
  random.effects <- (object$pval.tau2<0.05)
  if(random.effects){
    par.mle <- theta.mle[param]
    se.mle <- sqrt(object$vcov[param, param]) 
    rskovs <- rs+1/rs*log(us/rs)
    rtheta.skov <- predict(smooth.spline(values, rskovs), x=value)$y
  }
  else
    rtheta.skov <- rtheta
  
  if(alternative=="less"){
    pval.rtheta <- pnorm(rtheta)
    pval.rskov <- pnorm(rtheta.skov)
  }
  else if(alternative=="greater"){
    pval.rtheta <- pnorm(rtheta, lower.tail=FALSE)
    pval.rskov <- pnorm(rtheta.skov, lower.tail=FALSE)
  }
  else{
    pval.rtheta <- 2*pnorm(-abs(rtheta))
    pval.rskov <- 2*pnorm(-abs(rtheta.skov))
  }
  if(print){
    cat("\nSigned profile log-likelihood ratio test for parameter ", names(theta.mle[param]), sep="", "\n")
    if(random.effects){
      cat("\nFirst-order statistic")
      cat("\nr:", formatC(rtheta, digits), ", p-value:", formatC(pval.rtheta, digits), sep="")
      cat("\nSkovgaard's statistic")
      cat("\nrSkov:", formatC(rtheta.skov, digits), ", p-value:", formatC(pval.rskov, digits), sep="")
    }
    else{
      cat("\nr:", formatC(rtheta, digits), ", p-value:", formatC(pval.rtheta, digits), sep="")
    }
    if(alternative=="two.sided")
      cat("\nalternative hypothesis: parameter is different from ", round(value, digits), sep="", "\n")
    else
      cat("\nalternative hypothesis: parameter is ", alternative, " than ", round(value, digits), sep="", "\n")
  }
  ## bye
  ans <- c(rtheta=rtheta, pvalue.rtheta=pval.rtheta, rskov=rtheta.skov, pvalue.rskov=pval.rskov)
  invisible(ans)
}

coef.metaLik <- function(object, ...)
    object$mle[-length(object$mle)]

vcov.metaLik <- function(object, ...)
    object$vcov[-length(object$mle),-length(object$mle),drop=FALSE]

logLik.metaLik <- function(object, ...) {
  structure(object$max.lik, df = sum(sapply(object$mle, length)), class = "logLik")
}

model.matrix.metaLik <- function(object, ...) {

  rval <- if(!is.null(object$X)) object$X
  else model.matrix(object$terms, model.frame(object), contrasts = object$contrasts)
  return(rval)
}

residuals.metaLik <- function(object, type = c("pearson", "response", "working"), ...){

  mle <- object$mle
  npar <- length(object$mle)
  res <- object$y-object$fitted.values
  type <- match.arg(type)
  se <- sqrt(object$sigma2+mle[npar])
  switch(type, working=, response=res, pearson=res/se)
}
 
summary.metaLik <- function(object, ...){

  digits <- max(3, getOption("digits") - 3)
  if(class(object)!="metaLik")
    stop("\n'summary.metaLik' designed for 'metaLik' objects\n")
  beta <- coef(object)
  nbeta <- length(beta)
  beta.se <- sqrt(diag(as.matrix(vcov(object))))
  r <- matrix(nrow=nbeta, ncol=4)
  for(i in 1:nbeta)
    r[i,] <- test.metaLik(object, param=i, print=FALSE) 
  
  cat("\nLikelihood inference in random-effects meta-analysis models\n")
  cat("\nCall:\n", paste(deparse(object$call), sep = "\n", collapse = "\n"), "\n", sep = "")
  cat("Estimated heterogeneity parameter tau^2: ", formatC(object$tau2.mle, digits), " (p-value ", formatC(object$pval.tau2, digits), ")", sep="")
    if(object$pval.tau2<0.05){
      cat("\n\nFixed-effects:\n")
      ans <- cbind(beta, beta.se, r)
      dimnames(ans) <- list(names(beta), c("estimate", "std.err.", "signed logLRT", "p-value", "Skovgaard", "p-value"))
      ans <- round(ans, digits=digits)
    }
    else{
      cat("\n\nNo evidence of random-effects at 5% level, move to fixed-effects model")
      cat("\nFixed-effects:\n")
      ans <- cbind(beta, beta.se, r[,1], r[,2])
      dimnames(ans) <- list(names(beta), c("estimate", "std.err.", "signed logLRT", "p-value"))
      ans <- round(ans, digits=digits)
    }
  print.default(ans, print.gap = 2)
  cat("\nLog-likelihood:", format(round(object$max.lik, digits)), "\n")
  invisible(object)
}

profile.metaLik <- function(fitted, param=1, level=0.95, display=TRUE, ...){

  if(class(fitted)!="metaLik")
    stop("\nfunction designed for 'metaLik' objects")
  if(is.character(param)){
    pnames <- names(coef(fitted))
    param <- match(param, pnames, nomatch=NA)
  }
  if(missing(param) || is.na(param)){
    param <- 1L
        warning("\nassumed confidence interval for intercept")
  }    
  if(length(param)>1 || param>length(coef(fitted)) || !is.numeric(param))
    stop("\n'param' must be one single fixed-effects component")
  par.name <- names(coef(fitted))[param]

  pl <- .profLik(fitted, param=param)
  values <- pl$values
  rs <- pl$rs
  us <- pl$us
  random.effects <- (fitted$pval.tau2<0.05)
  if(random.effects){
    par.mle <- fitted$mle[param]
    se.mle <- sqrt(fitted$vcov[param, param]) 
    rskovs <- rs+1/rs*log(us/rs)
    rskovs <- predict(smooth.spline(values, rskovs), x=values)$y
  }
  else
    rskovs <- rs
  smooth.r <- smooth.spline(rs, values)
  smooth.rskov <- smooth.spline(rskovs, values)
  up.r <- predict(smooth.r, x=qnorm((1-level)/2))$y
  lo.r <- predict(smooth.r, x=qnorm((1+level)/2))$y
  up.rskov <- predict(smooth.rskov, x=qnorm((1-level)/2))$y
  lo.rskov <- predict(smooth.rskov, x=qnorm((1+level)/2))$y  
  
  if(display){
    if(random.effects)
      plot(smooth.spline(values, rs), type="l", ylim=c(-5,5), ylab="pivot", xlab=par.name, bty="l", col="blue")
    else{
       up.graph <- predict(smooth.rskov, x=-5)$y
       lo.graph <- predict(smooth.rskov, x=5)$y
      plot(smooth.spline(values, rs), type="l", ylim=c(-5,5), xlim=c(lo.graph, up.graph), ylab="pivot", xlab=par.name, bty="l", col="blue")
    }
    segments(lo.r, -5.5, lo.r, qnorm((1+level)/2), lty=2, col="blue")
    segments(up.r, -5.5, up.r, qnorm((1-level)/2), lty=2, col="blue")
    if(random.effects){
      lines(smooth.spline(values, rskovs), col="red")
      legend(mean(values), 4, c("First-order", "Skovgaard"), cex=0.8, col=c("blue", "red"), lty=c(1,1), bty="n")
      segments(lo.rskov, -5.5, lo.rskov, qnorm((1+level)/2), lty=2, col="red")
      segments(up.rskov, -5.5, up.rskov, qnorm((1-level)/2), lty=2, col="red")
    }   
    abline(h=qnorm((1-level)/2), lty=2, col='lightgrey')
    abline(h=qnorm((1+level)/2), lty=2, col='lightgrey')
  }
  tab <- matrix(c(lo.r, up.r, lo.rskov, up.rskov), ncol=2, byrow=TRUE)
  rownames(tab) <- c("signed logLRT", "Skovgaard")
  colnames(tab) <- c(paste(100*(1-level)/2, " %", sep=""), paste(100*(1+level)/2, " %", sep=""))
  cat("\nConfidence interval for parameter", par.name, "\n\n")
  if(fitted$pval.tau2<0.05)
    print(tab)
    else
      print(tab[1,])
  res <- structure(list(rthetas=rs, rskovs=rskovs, lower.rtheta=lo.r, upper.rtheta=up.r, lower.rskov=lo.rskov, upper.rskov=up.rskov))
  invisible(res)
}

.profLik <- function(object, param=1){

  if(class(object)!="metaLik")
    stop("\ninternal function designed for 'metaLik' objects")
  random.effects <- (object$pval.tau2<0.05)
  y <- object$y
  X <- object$X
  offset <- object$offset
  y <- y-offset 
  sigma2 <- object$sigma2
  ntheta <- length(object$mle)
  
  terms <- .likTerms(y, X, sigma2)
  lik <- terms$lik
  glik <- terms$glik
  Jmatrix <- terms$Jmatrix
  Imatrix <- terms$Imatrix
  Smatrix <- terms$Smatrix
  qvect <- terms$qvect

  .computeU <- function(th.mle, th.constr, id.par){
    A <- ( solve( Smatrix(th.mle, th.constr) )%*%qvect(th.mle, th.constr) )[id.par]
    B <- det( Jmatrix(th.mle) )^(.5)
    C <- det( solve(Imatrix(th.mle)) )
    D <- det( Smatrix(th.mle, th.constr) )
    E <- det( as.matrix(Jmatrix(th.constr)[-id.par,-id.par] ) )^(-.5)
    
    return( sign(th.mle[id.par]-th.constr[id.par])*abs(A*B*C*D*E) )
  }
     
  theta.mle <- object$mle
  par.mle <- theta.mle[param]
  se.mle <- sqrt(object$vcov[param, param]) 
  pts <- seq(-10, 10, by=.5)
  pts <- pts[pts!=0] # remove discontinuity point
  values <- par.mle+pts*se.mle
  rs <- us <- rep(NA, length(values))
  
  fixed <- rep(NA, ntheta)
  theta.constr <- fixed
  names(theta.constr) <- names(theta.mle)
  for(i in 1:length(values)){
    fixed[param] <- theta.constr[param] <- values[i]
    ynew <- y-as.matrix(X[,param])%*%values[i]
    Xnew <- as.matrix(X[,-param])
    if(random.effects){  
      if(NCOL(Xnew)>0){
        beta.start <- coef(lm.wfit(x=Xnew, y=ynew, w=1/sigma2))
        op <- optim(c(beta.start, var(y)), fn=lik, gr=glik, fixed=fixed, method="BFGS",
                      control=list(fnscale=-1, maxit=500)) 
        if(op$convergence) 
          op$par <- rep(NA, ntheta-1)
        theta.constr[is.na(fixed)] <- op$par
      }
      else{
        op <- optimise(f=lik, interval=c(0, 1e+6), maximum=TRUE, fixed=fixed)
        theta.constr[is.na(fixed)] <- op$maximum
      }
      ## likelihood ratio test statistic (and Skovgaard correction)
      if(all(is.finite(theta.constr)))
        lrt <- 2*(lik(theta.mle)-lik(theta.constr))
      else
        lrt <- NA
      if(is.finite(lrt) && lrt>0){
        rs[i] <- sign(theta.mle[param]-theta.constr[param])*sqrt(lrt)
        us[i] <- try(.computeU(theta.mle, theta.constr, param), silent=TRUE)
        if(inherits(us[i], "try-error"))
          us[i] <- NA
      }
      else
          rs[i] <- us[i] <- NA
    }
    else{ ## only fixed effects
      ## constrained maximum likelihood estimation
      if(NCOL(Xnew)>0){
        beta.constr <- coef(lm.wfit(x=Xnew, y=ynew, w=1/sigma2))
        theta.constr[is.na(fixed)] <- c(beta.constr, 0.0)
      }
      else
        theta.constr[is.na(fixed)] <- 0.0
      ## likelihood ratio test statistic
      if(all(is.finite(theta.constr)))
        lrt <- 2*(lik(theta.mle)-lik(theta.constr))
      else
        lrt <- NA
      if(is.finite(lrt) && lrt>0)
        rs[i] <- us[i] <- sign(theta.mle[param]-theta.constr[param])*sqrt(lrt)
      else
        rs[i] <- us[i] <- NA
    }
  }
  ok <- which(is.finite(rs) & is.finite(us))
  values <- values[ok]
  rs <- rs[ok]
  us <- us[ok]
  
  return( list(rs=rs, us=us, values=values) )
}
