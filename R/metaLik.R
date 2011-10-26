.likTerms <- function(y, X, sigma2){

    ntheta <- NCOL(X)+1
    ans <- list()
    ans$lik <- function(theta, fixed=rep(NA, ntheta)){

        all.theta <- fixed
        all.theta[is.na(fixed)] <- theta
        beta <- all.theta[-ntheta]
        tau2 <- all.theta[ntheta]
        v <- tau2+sigma2
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
        Info[1:(ntheta-1), 1:(ntheta-1)] <-  t(X)%*%diag(1/v)%*%X
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
    

metaLik <- function(formula, data, subset, contrasts = NULL, offset, sigma2){

    call <- match.call()
    if (missing(data)) 
        data <- environment(formula)
    mf <- match.call(expand.dots = FALSE)
    m <- match(c("formula", "data", "subset", "offset", "sigma2"), names(mf), 0L)
    mf <- mf[c(1L, m)]
    mf$drop.unused.levels <- TRUE
    mf[[1L]] <- as.name("model.frame")
    mf <- eval(mf, parent.frame())
    mt <- attr(mf, "terms")
    y <- model.response(mf, "any")
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
    if (!missing(subset))
        sigma2 <- sigma2[subset]
    
    lik <- .likTerms(y, X, sigma2)$lik
    glik <- .likTerms(y, X, sigma2)$glik
    Jmatrix <- .likTerms(y, X, sigma2)$Jmatrix

    ## compute DL estimates
    D <- diag(sigma2, ncol=NROW(X), nrow=NROW(X))
    P <- diag(NROW(X)) - X%*%solve(t(X)%*%solve(D)%*%X)%*%t(X)%*%solve(D)
    q.stat <- t(y)%*%t(P)%*%solve(D)%*%P%*%y
    t.value <- (q.stat-NROW(X)+NCOL(X))/(sum(diag(solve(D))) - sum(diag( solve(t(X)%*%solve(D)%*%X)%*%t(X)%*%solve(D)^2%*%X )))
    tau2.dl <- max(0, t.value)
    weights.dl <- diag(tau2.dl, ncol=NROW(X), nrow=NROW(X)) + D
    theta.dl <- solve(t(X)%*%solve(weights.dl)%*%X)%*%t(X)%*%solve(weights.dl)%*%y
    var.dl <- solve(t(X)%*%solve(weights.dl)%*%X)

    ## compute MLE
    start.theta <- c(theta.dl, ifelse(tau2.dl>0.2, tau2.dl, .2))
    op <- optim(start.theta, fn=lik, gr=glik, method="L-BFGS-B", lower=c(rep(-Inf, NCOL(X)), 0), control=list(fnscale=-1))
    if(op$convergence)
        stop("optim: convergence not reached.\n")
    theta.mle <- op$par
    vcov.mle <- try( solve(Jmatrix(theta.mle)) )
    if(inherits(vcov.mle, "try-error") || any(diag(vcov.mle)<=0))
       stop("convergence not reached, perhaps too few studies.\n")
    names(theta.mle) <-colnames(vcov.mle) <- rownames(vcov.mle) <- c(colnames(X), "tau^2")
    fitted.values <- X%*%theta.mle[1:NCOL(X)]
    
    ## exit
    m <- structure(list(y=y+offset, X=X, fitted.values=fitted.values, sigma2=sigma2, K=NROW(X), mle=theta.mle, vcov=vcov.mle, max.lik=op$value, DL=theta.dl, tau2.DL=tau2.dl, vcov.DL=var.dl, call=call, formula=formula, terms=mt, data=data,  offset=offset, contrasts = attr(X, "contrasts"), xlevels = .getXlevels(mt, mf), model=mf), class="metaLik")
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
  cat("Maximized log-likelihood:\n")
  print.default(format(x$max.lik, digits=digits),
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
    param <- as.integer(param)
    alternative <- match.arg(alternative)
    if(!missing(value) && (length(value)!= 1 || is.na(value)))
        stop("\n'value' must be a single number")
    if(class(object)!="metaLik")
        stop("\n'object' must be a metaLik object")
    if(!missing(param) && (length(param)!= 1 || is.na(param)))
        stop("\n'param' must be a single (integer) number")
    y <- object$y
    X <- object$X
    offset <- object$offset
    y <- y-offset 
    sigma2 <- object$sigma2
    ntheta <- NCOL(X)+1
    theta.mle <- object$mle
    if(param>=ntheta || param<=0)
        stop("\n'param' must be the index of one fixed effect parameter")
   
    ## constrained maximum likelihood estimation
    lik <- .likTerms(y, X, sigma2)$lik
    glik <- .likTerms(y, X, sigma2)$glik
    Jmatrix <- .likTerms(y, X, sigma2)$Jmatrix
    Imatrix <- .likTerms(y, X, sigma2)$Imatrix
    Smatrix <- .likTerms(y, X, sigma2)$Smatrix
    qvect <- .likTerms(y, X, sigma2)$qvect
    
    fixed <- rep(NA, ntheta)
    fixed[param] <- value
    op <- optim(c(rep(0, ntheta-2), 0.5), fn=lik, gr=glik, fixed=fixed, method="L-BFGS-B", lower=c(rep(-Inf, NCOL(X)-1), 0), control=list(fnscale=-1))
    if(op$convergence)
        stop("\n'optim': convergence not reached")
    theta.constr <- fixed
    theta.constr[is.na(fixed)] <- op$par
    names(theta.constr) <- names(theta.mle) 
    
    ## likelihood ratio test statistic (and Skovgaard correction)
    rtheta <- sign(theta.mle[param]-theta.constr[param])*sqrt(2*(lik(theta.mle)-lik(theta.constr))) 
    A <- ( solve( Smatrix(theta.mle, theta.constr) )%*%qvect(theta.mle, theta.constr) )[param]
    B <- sqrt( det(Jmatrix(theta.mle)) )
    C <- 1/det( Imatrix(theta.mle) )
    D <- det( Smatrix(theta.mle, theta.constr) )
    E <- 1/sqrt( det( Jmatrix(theta.constr)[-param,-param] ) )
    u <- A*B*C*D*E
    rskov <- as.numeric(rtheta+1/rtheta*log(u/rtheta))
    if(alternative=="less"){
        pval.rtheta <- pnorm(rtheta)
        pval.rskov <- pnorm(rskov)
    }
    else if(alternative=="greater"){
         pval.rtheta <- pnorm(rtheta, lower.tail=FALSE)
         pval.rskov <- pnorm(rskov, lower.tail=FALSE)
    }
    else{
        pval.rtheta <- 2*pnorm(-abs(rtheta))
        pval.rskov <- 2*pnorm(-abs(rskov))
    }
    if(print){
        cat("\nSigned profile log-likelihood ratio test for parameter ", names(theta.mle[param]), sep="", "\n")
        cat("\nFirst-order statistic")
        cat("\nr:", formatC(rtheta, digits), ", p-value:", formatC(pval.rtheta, digits), sep="")
        cat("\nSkovgaard's statistic")
        cat("\nrSkov:", formatC(rskov, digits), ", p-value:", formatC(pval.rskov, digits), sep="")
        if(alternative=="two.sided")
            cat("\nalternative hypothesis: parameter is different from ", round(value, digits), sep="", "\n")
        else
            cat("\nalternative hypothesis: parameter is ", alternative, " than ", round(value, digits), sep="", "\n")
    }
    ## bye
    ans <- c(rtheta=rtheta, pvalue.rtheta=pval.rtheta, rskov=rskov, pvalue.rskov=pval.rskov)
    invisible(ans)
}
   
coef.metaLik <- function(object, ...)
    object$mle

vcov.metaLik <- function(object, ...)
    object$vcov

logLik.metaLik <- function(object, ...) {
  structure(object$max.lik, df = sum(sapply(object$mle, length)), class = "logLik")
}

model.matrix.metaLik <- function(object, ...) {

    rval <- if(!is.null(object$X)) object$X
    else model.matrix(object$terms, model.frame(object), contrasts = object$contrasts)
    return(rval)
}

residuals.metaLik <- function(object, type = c("pearson", "response", "working"), ...){

  mle <- coef(object)
  npar <- length(mle)
  res <- object$y-object$fitted.values
  type <- match.arg(type)
  se <- sqrt(object$sigma2+mle[npar])
  switch(type, working=, response=res, pearson=res/se)
}
 
summary.metaLik <- function(object, ...){

    digits <- max(3, getOption("digits") - 3)
    if(class(object)!="metaLik")
        stop("\n'summary.metaLik' designed for 'metaLik' objects\n")
    theta <- coef(object)
    ntheta <- length(theta)
    se <- sqrt(diag(vcov(object)))
    r <- matrix(nrow=(ntheta-1), ncol=4)
    for(i in 1:(ntheta-1))
        r[i,] <- test.metaLik(object, param=i, print=FALSE)

    cat("\nLikelihood inference in random effects meta analysis models\n")
    cat("\nCall:\n", paste(deparse(object$call), sep = "\n", collapse = "\n"), "\n", sep = "")
    cat("Estimated heterogeneity component tau^2: ", formatC(theta[ntheta], digits), " (std.err. ", formatC(se[ntheta], digits), ")", sep="")
    cat("\nFixed effects:\n")
    ans <- cbind(theta[-ntheta], se[-ntheta], r)
    dimnames(ans) <- list(names(theta)[-ntheta], c("estimate", "std.err.", "signed logLRT", "p-value", "Skovgaard", "p-value"))
    ans <- round(ans, digits=digits)
    print.default(ans, print.gap = 2)
    cat("\nLog-likelihood:", format(round(object$max.lik, digits)), "\n")
    invisible(object)
}

profile.metaLik <- function(fitted, param=1, level=0.95, display=TRUE, ...){

    if(class(fitted)!="metaLik")
        stop("\nfunction designed for 'metaLik' objects")
    if(length(param)>1 || param>=length(fitted$mle) || !is.numeric(param))
        stop("\n'param' must be the index of one single fixed-effects component")
    if (missing(param)){
        param <- 1
        warning("\nassumed confidence interval for intercept")
    }
    par.mle <- fitted$mle[param]
    se.mle <- sqrt(fitted$vcov[param, param])
    values <- seq(from=par.mle-10*se.mle, to=par.mle+10*se.mle, length=30)
    rs <- rskovs <- rep(NA, length(values))
    for(i in 1:length(values)){
        test.res <- try(test.metaLik(fitted, param, values[i], print=FALSE))
        if(!inherits(test.res, "try-error")){
            rs[i] <- test.res["rtheta"]
            rskovs[i] <- test.res["rskov"]
        }
    }
    smooth.r <- smooth.spline(rs, values)
    smooth.rskov <- smooth.spline(rskovs, values)
    up.r <- predict(smooth.r, x=qnorm((1-level)/2))$y
    lo.r <- predict(smooth.r, x=qnorm((1+level)/2))$y
    up.rskov <- predict(smooth.rskov, x=qnorm((1-level)/2))$y
    lo.rskov <- predict(smooth.rskov, x=qnorm((1+level)/2))$y
    par.name <- names(coef(fitted))[param]

    if(display){
        plot(smooth.spline(values, rs), type="l", ylim=c(min(rs, rskovs), max(rs, rskovs)), ylab="pivot", xlab=par.name, bty="n")
        lines(smooth.spline(values, rskovs), col="red")
        legend(max(up.r, up.rskov), max(rs, rskovs), c("First-order statistic", "Skovgaard's statistic"), cex=0.8, col=c("black", "red"), lty=c(1,1))
        segments(lo.r, min(rs, rskovs)-10, lo.r, qnorm((1+level)/2), lty=2)
        segments(up.r, min(rs, rskovs)-10, up.r, qnorm((1-level)/2), lty=2)
        segments(lo.rskov, min(rs, rskovs)-10, lo.rskov, qnorm((1+level)/2), lty=2, col="red")
        segments(up.rskov, min(rs, rskovs)-10, up.rskov, qnorm((1-level)/2), lty=2, col="red")
        abline(h=qnorm((1-level)/2), lty=2, col='lightgrey')
        abline(h=qnorm((1+level)/2), lty=2, col='lightgrey')
      }
    tab <- matrix(c(lo.r, up.r, lo.rskov, up.rskov), ncol=2, byrow=TRUE)
    rownames(tab) <- c("signed logLRT", "Skovgaard")
    colnames(tab) <- c(paste(100*(1-level)/2, "%", sep=""), paste(100*(1+level)/2, "%", sep=""))
    print(tab)

    res <- structure(list(rthetas=rs, rskovs=rskovs, lower.rtheta=lo.r, upper.rtheta=up.r, lower.rskov=lo.rskov, upper.rskov=up.rskov))
    invisible(res)
}
