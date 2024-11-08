library(dplyr)
library(purrr)
library(lavaan)
library(lmerTest)
library(reshape2)
library(tidyr)
library(tidyverse)
library(data.table)
library(survival)
library(survminer)
library(rms)
library(forestploter)
library(tableone)
library(survival)
library(cmprsk)
library(tidycmprsk)
library(interactionR)
library(visreg)
library(tableone)
library(mice)

setwd('~') 
load(file = 'data.mort.RData')
data = data.mort
data[data == ''] <- NA

# functions we need
var_na_ratio <- function(x){
  return(mean(is.na(x)))
}
var_min <- function(x){
  if(sum(is.na(x)) < 2){
    out <- min(x, na.rm = T)
  }else{ out <- NA}
  return(out)
}
var_mean <- function(x){
  return(mean(x, na.rm = T))
}


tau <- as.Date("2022-11-30")
data$eventtime <- as.Date(apply(cbind(data$death_date, tau), 1, var_min), origin = '1970-01-01') - as.Date(data$enroll_date, origin = "1970-01-01") 
# status: death or not
data$status <- rep(0, length(data$eventtime))
data$status[which(!is.na(data$death_date) & (tau > data$death_date))] <- 1
data$status[(data$lost_date < data$death_date)] <- 0
data$staca <- data$status
data$staca[data$cancer_status == 0] <- 0
data$stacvd <- data$status
data$stacvd[data$CVD_status == 0] <- 0
data$stares <- data$status
data$stares[data$res_status == 0] <- 0
data$stadig <- data$status
data$stadig[data$dig_status == 0] <- 0
data$Smoke[data$Smoke == -3] <- NA
alcohol <- data$Alcohol
alcohol[data$Alcohol == -3] <- NA
data$Alcohol <- alcohol

# Data preparation
data.cox <- data.frame(eid = data$eid, time = as.numeric(data$eventtime), status = data$status, staca = data$staca, stacvd = data$stacvd, stares = data$stares, stadig = data$stadig,
                       WBWM = data$waterm, age = data$enroll_age, weight = data$weight, bmi = data$BMI, sex = as.factor(data$sex), height = sqrt(data$weight/data$BMI)*100,
                       edu = as.factor(data$edu), ethnic = data$ethnic_code, TDI = data$TDI, diet = data$healthy_diet,
                       smoke = as.factor(data$Smoke), alcohol = as.factor(data$Alcohol), longill = data$long_illness, fruit = data$fresh_fruit, vege = data$vegetables, redmeat = data$red_meat_cat, promeat = data$Processed_meat, physical = data$physical,
                       diabetes = as.factor(data$diabetes), hypertension = as.factor(data$hypertension), cancer = data$cancer_first, CVD = data$CVD_first_0, kidney = data$kidney_first_0,
                       cancer_status = data$cancer_status, CVD_status = data$CVD_status, res_status = data$res_status, dig_status = data$dig_status)
relevel(data.cox$smoke, ref="0") -> data.cox$smoke
relevel(data.cox$alcohol, ref="1") -> data.cox$alcohol
cancer = as.numeric(which(data.cox$cancer=='1'))
CVD = as.numeric(which(data.cox$CVD=='1'))
kidney = as.numeric(which(data.cox$kidney=='1'))
data.cox <- data.cox[!is.na(data.cox$WBWM),]
data.cox0 <- data.cox[data.cox$sex == 0, ]
data.cox1 <- data.cox[data.cox$sex == 1, ]
WBWMd <- rep(0, nrow(data.cox))
WBWMd[data.cox$sex == 0] <- cut(data.cox0$WBWM, breaks = quantile(data.cox0$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = FALSE, labels = c('Low', 'Medium', 'High'))
WBWMd[data.cox$sex == 1] <- cut(data.cox1$WBWM, breaks = quantile(data.cox1$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = FALSE, labels = c('Low', 'Medium', 'High'))
data.cox$WBWMd <- factor(WBWMd, levels = c(1, 2, 3), labels = c('Low', 'Medium', 'High'))
relevel(data.cox$WBWMd, ref="Medium") -> data.cox$WBWMd

# All
data.cox$cumhaz <- nelsonaalen(data.cox, time, status)
init = mice(data.cox, maxit=0)
meth = init$method
predM = init$predictorMatrix
predM[, c('eid', 'time', 'status', 'staca', 'stacvd', 'stares', 'stadig', 'WBWMd', 'height', 'weight',
          'cancer', 'CVD', 'kidney', 'cancer_status', 'CVD_status', 'res_status', 'dig_status')] = 0
meth[c('eid', 'time', 'status', 'staca', 'stacvd', 'stares', 'stadig', 'WBWMd', 
       'cancer', 'CVD', 'kidney', 'cancer_status', 'CVD_status', 'res_status', 'dig_status')]=""
data.imp <- mice(data.cox, method = meth, predictorMatrix=predM, m = 5, print = F)
save(data.imp, file = 'data.imp.RData')


# Data 
load('data.imp.RData')

# Functions
# pool.sub.fun: function used to pool the estimates with subgroups of M imputed datasets
# eg: pool.sub.fun(data, mod, cc, method = 1)
pool.sub.fun <- function(data, mod, cc, method){
  
  # data: imputed data
  # mod: model used 
  # cc: subset condition index
  # method: method used to pool data
  
  if(method == 1){
    cond <- conds1[cc]
    Q_set <- NULL
    U_set <- list()
    M <- data$m
    for (i in 1:M) {
      data_i <- complete(data, i)
      data_i$staoth <- data_i$status
      data_i$staoth[data_i$stacvd == 1 | data_i$staca == 1] <- 0
      data_i0 <- data_i[data_i$sex == 0, ]
      data_i1 <- data_i[data_i$sex == 1, ]
      WBWMd <- rep(0, nrow(data_i))
      WBWMd[data_i$sex == 0] <- cut(data_i0$WBWM, breaks = quantile(data_i0$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      WBWMd[data_i$sex == 1] <- cut(data_i1$WBWM, breaks = quantile(data_i1$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      data_i$WBWMd <- factor(WBWMd, levels = c(1, 2, 3), labels = c('Low', 'Medium', 'High'))
      relevel(data_i$WBWMd, ref="Medium") -> data_i$WBWMd
      data_i$wt.res[data_i$sex == 0] = lm(weight~WBWM, data = data_i0)$residuals
      data_i$wt.res[data_i$sex == 1] = lm(weight~WBWM, data = data_i1)$residuals
      data_i$bmid = factor(cut(data_i$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity')))
      if(cond == 'All'){
        data.sub = data_i
      } else{
        data.sub <- data_i[eval(parse(text = cond)), ] 
      }
      fit_i <- coxph(formula = as.formula(mod), data = data.sub)
      print(cox.zph(fit_i, transform = rank))
      print(car::vif(fit_i))
      U_i <- vcov(fit_i)
      Q_set <- bind_rows(Q_set, coefficients(fit_i))
      U_set[[i]] <- U_i
    }
    Qm <- matrix(apply(Q_set, 2, mean), ncol = 1)
    SUM_Um <- 0
    SUM_Bm <- 0
    for (i in 1:M) {
      SUM_Um <- SUM_Um + U_set[[i]]
      SUM_Bm <- SUM_Bm + (matrix(unlist(Q_set[i, ]), ncol = 1) - Qm) %*%
        t(matrix(unlist(Q_set[i, ]), ncol = 1) - Qm)
    }
    Um <- SUM_Um / M
    Bm <- SUM_Bm / (M - 1)
    Tm <- Um + (1 + 1 / M) * Bm
    
    se <- sqrt(diag(Tm))
    rm <- (1 + 1 / M) * diag((Bm / Tm))
    t <- Qm / se
    p.value <- (1-pnorm(abs(t), 0, 1))*2
    lwr <- Qm - qnorm(p = 0.975, 0, 1) * se
    upr <- Qm + qnorm(p = 0.975, 0, 1) * se
    res <- data.frame(estimate = Qm, expest = exp(Qm), explwr = exp(lwr), expupr = exp(upr), lwr = lwr, upr = upr, std.error = se, t = t, p.value = p.value)
  }
  
  if(method == 2){
    cond <- conds2[cc]
    if(cond == 'All'){
      fit <- with(data, coxph(formula = as.formula(mod)))
    }else{
      fit <- with(data, {
        coxph(formula = as.formula(mod), sub = eval(parse(text = cond)))})
    }
    res <- summary(pool(fit))
  }
  
  return(res)
}

# dose.response: function used to plot the dose-response relationship
# eg: dose.response(data, mod1, mod2, c('', 'WBWM (kg)'), cc, method = 2)
dose.response <- function(data, mod, names, cc1, cc2, method, cause = ''){
  
  # data: imputed data with M datasets
  # model1: model used in coxph
  # model2: model used in cph
  # names: x-axis labels and the title
  # cc1, cc2: subset condition index
  # method: method used to pool the estimates
  
  model1 <- mod[1]
  model2 <- mod[2]
  model3 <- mod[3]
  
  data.sub$staoth <- data.sub$status
  data.sub$staoth[data.sub$stacvd == 1 | data.sub$staca == 1] <- 0
  data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
  data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
  relevel(data.sub$bmid, ref="Normal weight") -> data.sub$bmid
  Mod <- cph(formula = as.formula(model2), data = data.sub)
  pooled <- pool.sub.fun(data, model1, cc1, method)
  name <- names(Mod$coefficients)
  Mod$coefficients <- pooled$estimate
  names(Mod$coefficients) <- name
  pval <- pooled$p.value[2]
  diag(Mod$var) <- pooled$std.error^2
  
  tiff( 
    filename = paste(cause, "_", names[1], ".tiff", sep = ''), 
    width = 12,            
    height = 11.5,           
    units = "cm",          
    bg = "white", res = 600)
  par(mfrow = c(1, 1))
  par(mar = c(4,4,4,4))
  ## plot
  if(names[1] == ''){
    Pre1 <- rms::Predict(Mod, aWBWM,
                         fun=exp, ref.zero=T, conf.int = 0.95)
    hist(data.sub$aWBWM, axes=F, xlab="", ylab="", breaks = 55,
         col = col[1], main=names[1],border = 'gray', freq = F)
  }else{
    Pre1 <- rms::Predict(Mod, WBWM,
                         fun=exp, ref.zero=T, conf.int = 0.95)
    hist(data.sub$WBWM, axes=F, xlab="", ylab="", breaks = 55,
         col = col[1], main=cause, cex.main = 1, border = 'gray', freq = F)
  }
  
  ### histogram
  axis(4, cex.axis = 0.8)
  par(new=T)
  ### nonlinear curve
  plot(Pre1[,1],axes=T,Pre1$yhat,type='l',lty=1,lwd=2,col=col[2],cex.axis=0.8,
       ylim=c(0,4),
       xlab=names[2],
       ylab='')
  col2 <- rgb(1, 0, 0, alpha=0.15)
  polygon(c(Pre1[,1], rev(Pre1[,1])),
          c(Pre1$lower, rev(Pre1$upper)),
          col = col2, border = col2)
  if(names[1] == 'Female'){
    text <- 'HR (95%CI)'
    mtext(text, side=2, line = 3, cex = 1, outer = F)
  }
  if(names[1] == 'Male'){
    text <- 'Probability density'
    mtext(text, side=4, line = 3, cex = 1, outer = F)
  }
  abline(h=1,col="#BFBFBF",lty=2, lwd=2)
  legend("topright",
         paste0("P-nonlinear",ifelse(round(pval,3) < 0.001," < 0.001", paste0(' = ',sprintf('%0.3f', pval)))),
         bty="n",cex=0.8, col = par("#2f4e87"), adj = c(0, 0.5))
  if(names[1] == ''){
    points(x = dd$limits$aWBWM[2],y=1,
           pch = 19,col = 'orange') 
    abline(v = dd$limits$aWBWM[2], lty=2, lwd=2)
  }else{
    points(x = dd$limits$WBWM[2],y=1,
           pch = 19,col = 'orange') 
    abline(v = dd$limits$WBWM[2], lty=2, lwd=2, col = "#2f4e87")
  }
  
  dev.off()
  
}

# Models
data.kkk = complete(data.imp, 1)
lm.mod <- c('weight ~ WBWM', 'weight ~ WBWMd', 'weight ~ aWBWM')
cox.mod = c(sprintf("Surv(time, status) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strata(age)', 'wt.res', 'height', 'edu', 'ethnic', 'TDI',  'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, status) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strat(age)', 'wt.res', 'height', 'edu', 'ethnic', 'TDI', 'strat(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strat(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, status) ~ %s", paste(c('WBWM', 'strata(age)', 'wt.res', 'height', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")))
cox.mod = c(sprintf("Surv(time, status) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI',  'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, status) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strat(age)', 'strat(bmid)', 'edu', 'ethnic', 'TDI', 'strat(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strat(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, status) ~ %s", paste(c('WBWM', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")))
conds1 <- c('All', 'data_i$sex == 1', 'data_i$sex == 0', 'data_i$age < 65', 'data_i$age < 65', 'data_i$ethnic == 0', 'data_i$ethnic == 1', 'data_i$longill == 0', 'data_i$longill == 1')
conds2 <- c('All', 'sex == 1', 'sex == 0', 'age < 65', 'age < 65', 'ethnic == 0', 'ethnic == 1', 'longill == 0', 'longill == 1')
conds3 <- c(paste('data_i$sex == 1 & data_i$WBWM <= ', median(data.kkk$WBWM[data.kkk$sex == 1]), sep = ''), paste('data_i$sex == 1 & data_i$WBWM > ', median(data.kkk$WBWM[data.kkk$sex == 1])),
            paste('data_i$sex == 0 & data_i$WBWM <= ', median(data.kkk$WBWM[data.kkk$sex == 0])), paste('data_i$sex == 0 & data_i$WBWM > ', median(data.kkk$WBWM[data.kkk$sex == 0])))

# Analysis
par(mfrow = c(1, 1))
col=c('#E0E7F2','#EE947B')


# Overall
data.kkk = complete(data.imp, 1)

# Female
sub = which(data.kkk$sex == 0)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
relevel(data.sub$bmid, ref="Normal weight") -> data.sub$bmid
dd <- datadist(data.sub) 
options(datadist='dd')
# data = data.imp; mod = cox.mod; names = c('Female', 'WBWM (kg)'); cc1 = 3; cc2 = c(3,4); method = 1; cause = 'All-cause'
dose.response(data.imp, cox.mod, names = c('Female', 'WBWM (kg)'), cc1 = 3, cc2 = c(3,4), method = 1, cause = 'All causes')

# Male
sub = which(data.kkk$sex == 1)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
relevel(data.sub$bmid, ref="Normal weight") -> data.sub$bmid
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.imp, cox.mod, names = c('Male', 'WBWM (kg)'), cc1 = 2, cc2 = c(1,2), method = 1, cause = 'All causes')

###############################
# CVD
par(mfrow = c(1, 1))
cox.mod = c(sprintf("Surv(time, stacvd) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI',  'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, stacvd) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strat(age)', 'strat(bmid)', 'edu', 'ethnic', 'TDI', 'strat(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strat(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, stacvd) ~ %s", paste(c('WBWM', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")))
data.cvd = data.imp
data.kkk = complete(data.cvd, 1)

# Female
sub = which(data.kkk$sex == 0)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.cvd, cox.mod, names = c('Female', 'WBWM (kg)'), cc1 = 3, cc2 = c(3,4), method = 1, cause = 'CVD')

# Male
sub = which(data.kkk$sex == 1)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.cvd, cox.mod, names = c('Male', 'WBWM (kg)'), cc1 = 2, cc2 = c(1,2), method = 1, cause = 'CVD')

###############################
# Cancer
par(mfrow = c(1, 1))
cox.mod = c(sprintf("Surv(time, staca) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI',  'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, staca) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strat(age)', 'strat(bmid)', 'edu', 'ethnic', 'TDI', 'strat(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strat(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, staca) ~ %s", paste(c('WBWM', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")))
data.ca = data.imp
data.kkk = complete(data.ca, 1)

# Female
sub = which(data.kkk$sex == 0)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.ca, cox.mod, names = c('Female', 'WBWM (kg)'), cc1 = 3, cc2 = c(3,4), method = 1, cause = 'Cancer')

# Male
sub = which(data.kkk$sex == 1)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.ca, cox.mod, names = c('Male', 'WBWM (kg)'), cc1 = 2, cc2 = c(1,2), method = 1, cause = 'Cancer')

###############################
# Other
#par(mfrow = c(1, 2))
cox.mod = c(sprintf("Surv(time, staoth) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strata(age)', 'strata(bmid)',  'edu', 'ethnic', 'TDI',  'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, staoth) ~ %s", paste(c('rcs(WBWM, quantile(WBWM)[2:4])', 'strat(age)', 'strat(bmid)', 'edu', 'ethnic', 'TDI', 'strat(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strat(cancer)', 'kidney'), collapse = " + ")),
            sprintf("Surv(time, staoth) ~ %s", paste(c('WBWM', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")))
data.oth = data.imp
data.kkk = complete(data.oth, 1)
data.kkk$staoth = data.kkk$status
data.kkk$staoth[data.kkk$staca == 1 | data.kkk$stacvd == 1] <- 0
# Female
sub = which(data.kkk$sex == 0)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.oth, cox.mod, names = c('Female', 'WBWM (kg)'), cc1 = 3, cc2 = c(3,4), method = 1, cause = 'Other causes')

# Male
sub = which(data.kkk$sex == 1)
data.sub = data.kkk[sub,]
data.sub$wt.res <- lm(weight~WBWM, data = data.sub)$residuals
data.sub$bmid = factor(cut(data.sub$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf)), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity'))
dd <- datadist(data.sub) 
options(datadist='dd')
dose.response(data.oth, cox.mod, names = c('Male', 'WBWM (kg)'), cc1 = 2, cc2 = c(1,2), method = 1, cause = 'Other causes')

