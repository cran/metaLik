.likTerms <- function(y, X, sigma2){

    nbeta <- ncol(X)
    ans <- list()
  
    ans$lik <- function(beta, tau2){

        if(!all(is.finite(beta)))
            return(NA)
        v <- tau2+sigma2
        res <- y-X%*%beta      
        as.numeric( -0.5*sum(log(v))-0.5*t(res)%*%diag(1/v)%*%res )
    }
    ans$prof.tau2 <- function(tau2){
        v <- sigma2+tau2
        beta <- coef( lm.wfit(x = X, y = y, w = 1/v) )
        res <- y-X%*%beta
        as.numeric( -0.5*sum(log(v))-0.5*t(res)%*%diag(1/v)%*%res )
    }
    ans$Jmatrix <- function(beta, tau2){
    
        npar <- nbeta+(tau2>0)
        Info <- matrix(0, ncol=npar, nrow=npar)
        v <- tau2+(sigma2)
        res <- y-X%*%beta
        Info[1:nbeta, 1:nbeta] <- t(X)%*%diag(1/v)%*%X
        if(tau2 > 0){
            Info[1:(npar-1), npar] <- t(X)%*%diag(1/v^2)%*%res
            Info[npar, 1:(npar-1)] <- Info[1:(npar-1), npar]
            Info[npar, npar] <- -0.5*sum(1/v^2)+t(res)%*%diag(1/v^3)%*%res
        }
    
        Info
    }
    ans$Imatrix <- function(beta, tau2){
      
        npar <- nbeta+(tau2>0)
        Info <- matrix(0, ncol=npar, nrow=npar)
        v <- tau2+sigma2
        Info[1:nbeta, 1:nbeta] <- t(X)%*%diag(1/v)%*%X
        if(tau2 > 0)
            Info[npar, npar] <- 0.5*sum(1/v^2) 
    
        Info
    }
    ans$Smatrix <- function(beta.mle, tau2.mle, beta.constr, tau2.constr){

        npar <- nbeta+1
        S <- matrix(0, ncol=npar, nrow=npar)
        v <- tau2.constr+sigma2
        S[1:(npar-1), 1:(npar-1)] <- t(X)%*%diag(1/v)%*%X
        S[1:(npar-1), npar] <- t(X)%*%diag(1/v^2)%*%X%*%(beta.mle-beta.constr)
        S[npar, npar] <- 0.5*sum(1/v^2) 
        
        S
    }
    ans$qvect <- function(beta.mle, tau2.mle, beta.constr, tau2.constr){

        npar <- nbeta+1 
        qvect <- rep(0.0, npar)
        v.mle <- tau2.mle+sigma2
        v.constr <- tau2.constr+sigma2
        qvect[1:(npar-1)] <- t(X)%*%diag(1/v.constr)%*%(X)%*%(beta.mle-beta.constr)
        qvect[npar] <- -0.5*sum(1/v.mle-1/v.constr)
        
        qvect
    }
    class(ans) <- c("lik.metaLik")
    ans
}

metaLik <- function(formula, data, subset, contrasts = NULL, offset, sigma2, weights=1/sigma2, level.tau2=0.05){
  
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
  N <- length(y)
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
      stop(gettextf("number of offsets is %d should equal %d (number of observations)", length(offset), length(y)), domain = NA)
  }
  if (is.null(offset)) 
    offset <- rep.int(0, length(y))
  y <- y-offset
  
  ## compute DL estimates
  D <- diag( 1/sigma2, ncol=NROW(X), nrow=NROW(X) )
  P <- diag( NROW(X)) - X %*%  solve(t(X) %*% D %*% X) %*%t (X) %*% D
  q.stat <- t(y) %*% t(P) %*% D %*% P %*%y
  t.value <- ( q.stat-NROW(X)+NCOL(X) ) / ( sum( diag(D) ) - sum( diag( solve( t(X) %*% D %*%X ) %*% t(X) %*% D^2 %*%X ) ) )
  tau2.dl <- max(0, t.value)
  weights.dl <- diag(1/(tau2.dl+sigma2), ncol=NROW(X), nrow=NROW(X))
  beta.dl <- solve( t(X) %*% weights.dl %*%X ) %*% t(X) %*% weights.dl %*%y
  var.dl <- solve( t(X) %*% weights.dl %*%X )

  ## MLE random effects model
  prof.tau2 <- .likTerms(y, X, sigma2)$prof.tau2
  tau2.mle <- optimize( prof.tau2, interval=c(0, 1e+4), maximum=TRUE)$maximum
  v <- sigma2+tau2.mle
  beta.mle <- coef( lm.wfit(x = X, y = y, w = 1/v) )

  ## MLE fixed effects model
  fit.fe <- lm(y ~ 0 + X, weights=1/sigma2)
  beta.fe <- coef(fit.fe)
  names(beta.fe) <- names(beta.mle)

  ## Cochran Q statistic for heterogeneity
  w.fe <- diag(1/sigma2)
  .invcalc <- function (X, W, k){
      sWX <- sqrt(W) %*% X
      res.qrs <- qr.solve(sWX, diag(k))
      return(tcrossprod(res.qrs))
  }
  stXWX <- .invcalc(X = X, W = w.fe, k = N)
  P <- w.fe - w.fe %*% X %*% stXWX %*% crossprod(X, w.fe)
  Q <- max(0, c(crossprod(y, P) %*% y))
  pval.tau2 <- ifelse(N - NCOL(X) >= 1, pchisq(Q, df = N - NCOL(X), lower.tail = FALSE), 1)

  terms <- .likTerms(y, X, sigma2)
  lik <- terms$lik
  Jmatrix <- terms$Jmatrix
  Imatrix <- terms$Imatrix
  
  vcov.mle <- try( solve(Jmatrix(beta.mle, tau2.mle)) )
  if(inherits(vcov.mle, "try-error") || any(diag(vcov.mle)<0)){
      vcov.mle <- try( solve(Imatrix(beta.mle, tau2.mle)) )
      if(inherits(vcov.mle, "try-error") || any(diag(vcov.mle)<0))
          stop("convergence not reached, perhaps too few studies.\n")
  }
  fitted.values <- X%*%beta.mle
  
  colnames(vcov.mle) <- rownames(vcov.mle) <- c(colnames(X), "tau^2")
  
  ## exit
  m <- structure(list(y=y+offset, X=X, fitted.values=fitted.values, sigma2=sigma2, K=NROW(X), mle=c(beta.mle, tau2.mle), vcov=vcov.mle, max.lik=lik(beta.mle, tau2.mle), beta.mle=beta.mle, tau2.mle=tau2.mle, pval.tau2=pval.tau2, level.tau2=level.tau2, Q=Q, DL=beta.dl, tau2.DL=tau2.dl, vcov.DL=var.dl, call=call, formula=formula, terms=mt,  offset=offset, contrasts = attr(X, "contrasts"), xlevels = .getXlevels(mt, mf), model=mf), class="metaLik")
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
  beta.mle <- coef(object)
  if(is.character(param)){
    pnames <- names(beta.mle)
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

  rtheta <- rtheta.skov <- predict(pl$smooth.rs, x=value)$y
  if(object$tau2.mle>0)
      rtheta.skov <- predict(pl$smooth.rskovs, x=value)$y
  
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
    cat("\nSigned profile log-likelihood ratio test for parameter ", names(beta.mle[param]), sep="", "\n")
    cat("\nFirst-order statistic")
    cat("\nr:", formatC(rtheta, digits), ", p-value:", formatC(pval.rtheta, digits), sep="")
    cat("\nSkovgaard's statistic")
    cat("\nrSkov:", formatC(rtheta.skov, digits), ", p-value:", formatC(pval.rskov, digits), sep="")
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
    object$beta.mle 

vcov.metaLik <- function(object, ...){
    nbeta <- length(object$beta.mle)
    object$vcov[1:nbeta,1:nbeta]
}
                
logLik.metaLik <- function(object, ...) {
  structure(object$max.lik, df = sum(sapply(object$mle, length))+(object$tau2.mle>0), class = "logLik")
}

model.matrix.metaLik <- function(object, ...) {

  rval <- if(!is.null(object$X)) object$X
  else model.matrix(object$terms, model.frame(object), contrasts = object$contrasts)
  return(rval)
}

residuals.metaLik <- function(object, type = c("pearson", "response", "working"), ...){

  res <- object$y-object$fitted.values
  type <- match.arg(type)
  se <- sqrt(object$sigma2+object$tau2.mle)
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
  tau2 <- object$tau2.mle
  
  cat("\nLikelihood inference in random-effects meta-analysis models\n")
  cat("\nCall:\n", paste(deparse(object$call), sep = "\n", collapse = "\n"), "\n", sep = "")
  cat("\nEstimated heterogeneity parameter tau2")
  if(object$tau2.mle > 1e-4)
      cat(" = ", formatC(unname(object$tau2.mle), digits), sep="")
   else
       cat(" < 0.0001")
   cat("\nTest for heterogeneity Q = ", formatC(unname(object$Q), digits), " (pval", sep="")
  if(object$pval.tau2 > 1e-4)
      cat(" = ", formatC(unname(object$pval.tau2), digits), ")", sep="")
  else
      cat(" < 0.0001)")
  if(object$pval.tau2 > object$level.tau2)
      cat("\nNo evidence of between-study heterogeneity, Skovgaard's statistic reduces to signed logLRT")
  
  cat("\n\nFixed-effects:\n")

  ans <- cbind(beta, beta.se, r)
  dimnames(ans) <- list(names(beta), c("estimate", "std.err.", "signed logLRT", "p-value", "Skovgaard", "p-value"))
  ans <- round(ans, digits=digits)
  
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

  up.r <-  up.rskov <- predict(pl$smooth.rs.inv, x=qnorm((1-level)/2))$y
  lo.r <- lo.rskov <- predict(pl$smooth.rs.inv, x=qnorm((1+level)/2))$y

  if(fitted$tau2.mle>0){
      up.rskov <- predict(pl$smooth.rskovs.inv, x=qnorm((1-level)/2))$y
      lo.rskov <- predict(pl$smooth.rskovs.inv, x=qnorm((1+level)/2))$y
  }
 
  if(display){
      pts <- seq(-5, 5, by=.5)
      values <- fitted$beta.mle[param] + pts * sqrt(fitted$vcov[param,param])
      toplot <- predict( pl$smooth.rs, x=values )
      plot(toplot, type="l", ylim=c(-5,5), ylab="pivot", xlab=par.name, col="blue")
      segments(lo.r, -5.5, lo.r, qnorm((1+level)/2), lty=2, col="blue")
      segments(up.r, -5.5, up.r, qnorm((1-level)/2), lty=2, col="blue")
      if(fitted$tau2.mle > 0 && fitted$pval.tau2 < fitted$level.tau2){
          toplot <-  predict( pl$smooth.rskovs, x=values )
          lines(toplot, col="red")
          segments(lo.rskov, -5.5, lo.rskov, qnorm((1+level)/2), lty=2, col="red")
          segments(up.rskov, -5.5, up.rskov, qnorm((1-level)/2), lty=2, col="red")
          legend(mean(values), 4, c("First-order", "Skovgaard"), cex=0.8, col=c("blue", "red"), lty=c(1,1), bty="n")
      }
      abline(h=qnorm((1-level)/2), lty=2, col='lightgrey')
      abline(h=qnorm((1+level)/2), lty=2, col='lightgrey')
  }
  tab <- matrix(c(lo.r, up.r, lo.rskov, up.rskov), ncol=2, byrow=TRUE)
  rownames(tab) <- c("signed logLRT", "Skovgaard")
  colnames(tab) <- c(paste(100*(1-level)/2, " %", sep=""), paste(100*(1+level)/2, " %", sep=""))
  cat("\nConfidence interval for parameter", par.name, "\n\n")
  print(tab)

  res <- structure(list(lower.rtheta=lo.r, upper.rtheta=up.r, lower.rskov=lo.rskov, upper.rskov=up.rskov))
  invisible(res)
}

.profLik <- function(object, param=1){

    if(class(object)!="metaLik")
        stop("\ninternal function designed for 'metaLik' objects")
    y <- object$y
    N <- length(y)
    X <- object$X
    offset <- object$offset
    y <- y-offset 
    sigma2 <- object$sigma2
    nbeta <- length(object$beta.mle)
    terms <- .likTerms(y, X, sigma2)
    lik <- terms$lik
    Jmatrix <- terms$Jmatrix
    Imatrix <- terms$Imatrix
    Smatrix <- terms$Smatrix
    qvect <- terms$qvect
     
    beta.mle <- object$beta.mle
    tau2.mle <- object$tau2.mle
    par.mle <- beta.mle[param]
    se.mle <- sqrt(object$vcov[param, param]) 
    pts <- c(seq(-5, -1, by=.5), seq(1, 5, by=.5))
    values <- par.mle+pts*se.mle
    rs <- us <- rep(NA, length(values))
  
    fixed <- rep(NA, nbeta)
    beta.constr <- fixed
    names(beta.constr) <- names(beta.mle)

    .computeU <- function(beta.mle, tau2.mle, beta.constr, tau2.constr, id.par){
        S <- Smatrix(beta.mle, tau2.mle, beta.constr, tau2.constr)
        q <- qvect(beta.mle, tau2.mle, beta.constr, tau2.constr)
        J.mle <- Jmatrix(beta.mle, tau2.mle)
        J.constr <- Jmatrix(beta.constr, tau2.constr)
        I.mle <- Imatrix(beta.mle, tau2.mle)
        
        A <- abs( solve(S) %*%q )[id.par]
        B <- abs( det( J.mle ) )^(.5)
        C <- abs( det( solve(I.mle) ) )
        D <- abs( det( S ) )
        E <- abs( det( as.matrix(J.constr[-id.par,-id.par] ) ) )^(-.5)
        
        return( sign(beta.mle[id.par]-beta.constr[id.par])*A*B*C*D*E )
    }
   
    for(i in 1:length(values)){
        fixed[param] <- beta.constr[param] <- values[i]
        ynew <- y-as.matrix(X[,param])%*%values[i]
        Xnew <- as.matrix(X[,-param])
        tau2.constr <- 0.0
        if(object$tau2.mle>0){
            prof.tau2 <- .likTerms(ynew, Xnew, sigma2)$prof.tau2
            tau2.constr <- optimize(prof.tau2, interval=c(0, 1e+4), maximum=TRUE)$maximum
        }
        if(NCOL(Xnew)>0){
            v <- sigma2+tau2.constr
            beta.hat <- coef( lm.wfit(x = Xnew, y = ynew, w = 1/v) )
            beta.constr[is.na(fixed)] <- beta.hat
        }

        ## likelihood ratio test statistic (and Skovgaard correction)
        lrt <- 2*(lik(beta.mle, tau2.mle)-lik(beta.constr, tau2.constr))

        if(is.finite(lrt) && lrt>0){
            rs[i] <- sign(beta.mle[param]-beta.constr[param])*sqrt(lrt)
            if(tau2.mle>0 && object$pval.tau2 < object$level.tau2){
                us[i] <- try(.computeU(beta.mle, tau2.mle, beta.constr, tau2.constr, param), silent=TRUE)
                if(inherits(us[i], "try-error"))
                    us[i] <- NA
            }
        }
    }
    smooth.rs <- smooth.rskovs <-  smooth.spline( x=values, y=rs )
    smooth.rs.inv <- smooth.rskovs.inv <- smooth.spline( y=values, x=rs )
    if(tau2.mle>0 && object$pval.tau2 < object$level.tau2){
        rskovs <- rs+1/rs*log(us/rs)
        smooth.rskovs <- smooth.spline( x=values, y=rskovs )
        smooth.rskovs.inv <- smooth.spline( y=values, x=rskovs )
    }

    return( list( smooth.rs=smooth.rs, smooth.rs.inv=smooth.rs.inv, smooth.rskovs=smooth.rskovs, smooth.rskovs.inv=smooth.rskovs.inv) )
}

simulate.metaLik <- function(object, nsim = 1, seed = NULL, DL = FALSE, ...){

    if (!exists(".Random.seed", envir = .GlobalEnv, inherits = FALSE)) 
        runif(1)
    if (is.null(seed)) 
        RNGstate <- get(".Random.seed", envir = .GlobalEnv)
    else {
        R.seed <- get(".Random.seed", envir = .GlobalEnv)
        set.seed(seed)
        RNGstate <- structure(seed, kind = as.list(RNGkind()))
        on.exit(assign(".Random.seed", R.seed, envir = .GlobalEnv))
    }
    if(!DL){
        ftd <- fitted(object)
        tau2 <- object$tau2.mle
    }
    else{ ## DL
        ftd <- object$X %*% object$DL
        tau2 <- object$tau2.DL
    }
    n <- length(ftd)
    nm <- names(ftd)

    val <- replicate(nsim, ftd + rnorm( n, sd = sqrt(object$sigma2+tau2) ) )
    val <- as.data.frame(val)
    colnames(val) <- paste("sim", seq_len(nsim), sep = "_")
    if (!is.null(nm)) 
        rownames(val) <- nm
    attr(val, "seed") <- RNGstate
    val
}
