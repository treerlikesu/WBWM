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
library(interactionR)
library(visreg)
library(epiR)
library(gt)
library(mice)
library(ggplot2)
library(grid)

setwd('~')
# Data
load('data.imp.RData')

# Functions
# pool.fun.sub: function used to pool the estimates with subgroups of M imputed datasets
# eg: pool.sub.fun(data, mod1, sub, cc1 = 1, cc2 = 2, method = 1)
pool.sub.fun <- function(data, mod, cc1, cc2, method){
  
  # data: imputed data
  # mod: model used 
  # cc1: subset condition index
  # cc2: index for sex
  # method: method used to pool data
  
  if(method == 1){
    cond <- conds1[cc1]
    Q_set <- NULL
    U_set <- list()
    M <- data$m
    for (i in 1:M) {
      data_i <- complete(data, i)
      data_i$WBWM <- as.numeric(data_i$WBWM)
      data_i0 <- data_i[data_i$sex == 0, ]
      data_i1 <- data_i[data_i$sex == 1, ]
      WBWMd <- rep(0, nrow(data_i))
      WBWMd[data_i$sex == 0] <- cut(data_i0$WBWM, breaks = quantile(data_i0$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      WBWMd[data_i$sex == 1] <- cut(data_i1$WBWM, breaks = quantile(data_i1$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      data_i$WBWMd <- factor(WBWMd, levels = c(1, 2, 3), labels = c('Low', 'Medium', 'High'))
      relevel(data_i$WBWMd, ref="Medium") -> data_i$WBWMd
      data_i$staoth <- data_i$status
      data_i$staoth[data_i$stacvd == 1 | data_i$staca == 1] <- 0
      data_i$wt.res = lm(weight~WBWM, data = data_i)$residuals
      data_i$bmid = factor(cut(data_i$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity')))
      data_i$bmid2 =  factor(cut(data_i$bmi, breaks = c(-Inf, 25, 30, Inf), labels = c('Underornormal', 'Overweight', 'Obesity')))
      data_i$aged <- factor(cut(data_i$age, breaks = c(0, 60, 90), include.lowest = T), labels = c('Young', 'Old'))
      if(cond == 'All'){
        data.sub = data_i
      } else{
        data.sub <- data_i[eval(parse(text = cond)), ] 
      }
      #data.sub$ff.res <- lm(fatfree~WBWM, data = data.sub)$residuals
      fit_i <- coxph(formula = as.formula(mod), data = data.sub)
      #print(cox.zph(fit_i, transform = 'rank'))
      #print(car::vif(fit_i))
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

# sub.test: functions used to calculate P for interation
sub.test <- function(data, lm.mod, cox.mod, cc){
  
  # data: data with M imputed datasets
  # lm.mod: linear model to calculate weight
  # cox.mod: model list include two models with or without interaction term
  cond = conds2[cc]
  cox.mod1 <- cox.mod[1]
  cox.mod2 <- cox.mod[2]
  cox1 <- with(data, {
    aged = cut(age, breaks = c(0, 60, 79), include.lowest = T)
    bmid = cut(bmi, breaks = c(-Inf, 18.5, 25, 30, Inf))
    bmid2 = cut(bmi, breaks = c(-Inf, 25, 30, Inf))
    wt.res = lm(as.formula(lm.mod))$residuals
    coxph(formula = as.formula(cox.mod1))
  })
  cox2 <- with(data, {
    aged = cut(age, breaks = c(0, 60, 79), include.lowest = T)
    bmid = cut(bmi, breaks = c(-Inf, 18.5, 25, 30, Inf))
    bmid2 = cut(bmi, breaks = c(-Inf, 25, 30, Inf))
    wt.res = lm(as.formula(lm.mod))$residuals
    coxph(formula = as.formula(cox.mod2))
  })
  res <- D2(cox1, cox2, use = 'likelihood')
  pval <- res$result[4]
  return(pval)
}

out.trans <- function(out){ 
  out <- sprintf('%0.3f', unlist(out))
  out.t <- c(paste(out[1], ' (', out[4], ', ', out[7], ')', sep = ''), paste(out[2], ' (', out[5], ', ', out[8], ')', sep = ''), paste(out[3], ' (', out[6], ', ', out[9], ')', sep = ''), out[10:12])
  return(out.t)
}

# sub.test: functions used to calculate P for interation
groups <- c('sex1', 'agedOld', 'hypertension1', 'diabetes1', 'longill1', 'bmi')
sub.test.mar <- function(data, lm.mod, cox.mod, cc, g){
  
  # data: data with M imputed datasets
  # lm.mod: linear model to calculate weight
  # cox.mod: model list include two models with or without interaction term
  # cc: index for model used
  # g: index for subgroups
  
  cond = conds2[cc]
  group = groups[g]
  mod <- cox.mod[1]
  data_i <- complete(data, 1)
  data_i$bmid2 = factor(cut(data_i$bmi, breaks = c(-Inf, 25, 30, Inf), labels = c('Underornormal', 'Overweight', 'Obesity')))
  data_i$bmid = factor(cut(data_i$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity')))
  data_i$aged <- factor(cut(data_i$age, breaks = c(0, 60, 90), include.lowest = T), labels = c('Young', 'Old'))
  Mod <- coxph(formula = as.formula(mod), data = data_i)
  res <- pool.sub.fun(data, mod, cc1 = 1, cc2 = 0, method = 1)
  name <- names(Mod$coefficients)
  Mod$coefficients <- res$estimate
  names(Mod$coefficients) <- name
  diag(Mod$var) <- res$std.error^2
  if(group != 'bmi'){
    out.lw = interactionR_delta(Mod, exposure_names = c('WBWMdLow', group))$df[7:9, -1]
    out.hw = interactionR_delta(Mod, exposure_names = c('WBWMdHigh', group))$df[7:9, -1]
    out <- rbind(c('Low WBWM', out.trans(out.lw)), c('High WBWM', out.trans(out.hw)))
    out = data.frame(out)
    colnames(out) <- c('WBWM', 'Multiplicative scale', 'RERIs (95% CIs)', 'APs (95% CIs)', 'p1', 'p2', 'p3')
    out <- out %>% mutate(group = rep(group, 2), .before = 1)
  }
  if(group == 'bmi'){
    out.lwov = interactionR_delta(Mod, exposure_names = c('WBWMdLow', 'bmid2Overweight'))$df[7:9, -1]
    out.hwob = interactionR_delta(Mod, exposure_names = c('WBWMdHigh', 'bmid2Obesity'))$df[7:9, -1]
    out.lwob = interactionR_delta(Mod, exposure_names = c('WBWMdLow', 'bmid2Obesity'))$df[7:9, -1]
    out.hwov = interactionR_delta(Mod, exposure_names = c('WBWMdHigh', 'bmid2Overweight'))$df[7:9, -1]
    out <- rbind(c('Low WBWM', out.trans(out.lwov)), c('High WBWM', out.trans(out.hwov)),
                 c('Low WBWM', out.trans(out.lwob)), c('High WBWM', out.trans(out.hwob)))
    out = data.frame(out)
    colnames(out) <- c('WBWM', 'Multiplicative scale', 'RERIs (95% CIs)', 'APs (95% CIs)', 'p1', 'p2', 'p3')
    out <- out %>% mutate(group = rep(c('Overweight', 'Obesity'), each = 2), .before = 1)
  }
  return(out)
}

# forest.data: used to prepare for forest plot
# eg: foerest(res0, index, range, name)
forest.data <- function(res0, index, range, name){
  
  # res0: pooled estimates 
  # index: index for model and name
  # range: 1:(WBWM groups - 1) 
  # name: low or high
  
  res1 <- data.frame(expesy = sprintf("%.3f", res0$expest), lwr = sprintf("%.3f", res0$explwr), upr = sprintf("%.3f", res0$expupr))
  res2 <- data.frame(expci = sprintf("%.3f (%.3f, %.3f)", res0$expest, res0$explwr, res0$expupr), pval = sprintf("%.3f", res0$p.value))
  res <- cbind(res1, res2)[range,]
  rownames(res) <- name[-length(name)]
  res.all <- rownames_to_column(res, var = "Characteristics")
  res.all <- cbind(Subgroup = c(NA, subname[index], NA), rbind(res.all, c(name[length(name)], rep(1, 3), 'Reference', NA)))
  res.all[, 5:6] <- lapply(res.all[, 5:6], as.character)
  return(res.all)
}

# Analysis
lm.mod <- c('weight ~ WBWM', 'weight ~ WBWMd', 'weight ~ aWBWM')
cox.mod = list(c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : sex', 'WBWMd', 'sex', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : aged', 'aged', 'WBWMd', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'aged', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : hypertension', 'WBWMd', 'ethnic', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'ethnic', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : diabetes', 'WBWMd', 'ethnic', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'ethnic', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : longill', 'WBWMd', 'longill', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'longill', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd : bmid2', 'bmid2', 'WBWMd', 'longill', 'strata(bmid)', 'strata(age)', 'sex', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'bmid2', 'strata(age)', 'sex', 'longill', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))))

cox.mod = list(c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * sex', 'strata(age)', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * aged', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'aged', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * hypertension', 'WBWMd', 'ethnic', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'ethnic', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * diabetes','ethnic', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'ethnic', 'strata(bmid)', 'edu', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * longill', 'strata(age)', 'sex', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'strata(age)', 'sex', 'longill', 'strata(bmid)', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))),
               c(sprintf("Surv(time, status) ~ %s", paste(c('WBWMd * bmid2', 'longill', 'strata(age)', 'sex', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + ")),
                 sprintf("Surv(time, status) ~ %s", paste(c('WBWMd', 'bmid2', 'strata(age)', 'sex', 'longill', 'edu', 'ethnic', 'TDI', 'strata(smoke)', 'alcohol', 'diet', 'physical', 'diabetes', 'hypertension', 'CVD', 'strata(cancer)', 'kidney'), collapse = " + "))))
model.set <- c('Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + strata(bmid) + sex + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + edu + ethnic + sex + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + edu + ethnic + sex + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, status) ~ WBWMd + strata(age) + edu + ethnic + sex + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney')

model.all <- c('Surv(time, status) ~ WBWMd + strata(age) + sex + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, stacvd) ~ WBWMd + strata(age) + sex + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, staca) ~ WBWMd + strata(age) + sex + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, staca) ~ WBWMd + strata(age) + sex + strata(bmid) + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney')

model.all <- c('Surv(time, status) ~ WBWMd + strata(age) + wt.res + height + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, stacvd) ~ WBWMd + strata(age) + wt.res + height + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, staca) ~ WBWMd + strata(age) + wt.res + height + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney',
               'Surv(time, staoth) ~ WBWMd + strata(age) + wt.res + height + edu + ethnic + TDI + strata(smoke) + alcohol + diet + physical + longill + diabetes + hypertension + CVD + strata(cancer) + kidney')
conds1 <- c('All', 'data_i$sex == 1', 'data_i$sex == 0', 'data_i$age < 60', 'data_i$age >= 60', 'data_i$hypertension == 1', 'data_i$hypertension == 0', 'data_i$diabetes == 1', 'data_i$diabetes == 0', 'data_i$longill == 1', 'data_i$longill == 0', 'data_i$bmi <25 & data_i$bmi>=18.5', 'data_i$bmi < 30 & data_i$bmi>=25', 'data_i$bmi >= 30')
conds2 <- c('All','sex == 0', 'sex == 1')
subname <- c('Overall', 'Male', 'Female','<60 ', paste('\u2265', 60, sep =''), 'Yes', 'No', 'Yes', 'No', 'Yes', 'No', '<25', '25—30', paste('\u2265', 30, sep =''))


# Subgroup test
# lm.mod <-lm.mod[1]; cox.mod = cox.mod[[3]]
# cc: index for sex
p.inter <- sprintf('%.3f', c(sub.test(data.imp, lm.mod[1], cox.mod[[1]], cc = 1), 
                             sub.test(data.imp, lm.mod[1], cox.mod[[2]], cc = 1),
                             sub.test(data.imp, lm.mod[1], cox.mod[[3]], cc = 1),
                             sub.test(data.imp, lm.mod[1], cox.mod[[4]], cc = 1),
                             sub.test(data.imp, lm.mod[1], cox.mod[[5]], cc = 1),
                             sub.test(data.imp, lm.mod[1], cox.mod[[6]], cc = 1)))
sub.inter <- rbind(sub.test.mar(data.imp, lm.mod[1], cox.mod[[1]], cc = 1, g = 1), 
                  sub.test.mar(data.imp, lm.mod[1], cox.mod[[2]], cc = 1, g = 2),
                  sub.test.mar(data.imp, lm.mod[1], cox.mod[[3]], cc = 1, g = 3),
                  sub.test.mar(data.imp, lm.mod[1], cox.mod[[4]], cc = 1, g = 4),
                  sub.test.mar(data.imp, lm.mod[1], cox.mod[[5]], cc = 1, g = 5),
                  sub.test.mar(data.imp, lm.mod[1], cox.mod[[6]], cc = 1, g = 6))

# Subgroup models
res.for <- list()
range <- 1:2; name <- c('Low', 'High', 'Medium')
for(i in seq(length(model.set))){
  res0 = pool.sub.fun(data.imp, model.set[i], cc1 = i, cc2 = 0, method = 1)
  res.for[[i]] <- forest.data(res0, i, range, name)
} 
res.for.table <- do.call(rbind, res.for)
colnames(res.for.table) <- c("Group", 'WBWM', 'HR', 'lower', 'upper', "HR (95%CI)", "P value")
dt <- res.for.table
dt[,-1] <- dt[c(3, 1:2, 6, 4:5, 9, 7:8, 12, 10:11, 15, 13:14,
                18, 16:17, 21, 19:20, 24, 22:23, 27, 25:26,
                30, 28:29, 33, 31:32, 36, 34: 35, 39, 37:38, 42, 40:41) ,-1]
dt[, 3:5] <- lapply(dt[, 3:5], as.numeric)
dt$`P value` <- ifelse(is.na(dt$`P value`) , "", dt$`P value` )
dt$`P value`[dt$`P value` == '0.000'] <- '<0.001'
dt$Group <- ifelse(is.na(dt$Group), "", dt$Group)
dt$Group <- ifelse(is.na(dt$`HR (95%CI)`), 
                   dt$Group, 
                   paste0("    ", dt$Group))
dt$`HR (95%CI)` <- ifelse(is.na(dt$`HR (95%CI)`) , "", dt$`HR (95%CI)` )
dt <- rbind(dt[1:3,], c('Sex', rep('', ncol(dt)-1)), dt[4:9,], c('Age (years)', rep('', ncol(dt)-1)), dt[10:15,], c('Hypertension', rep('', ncol(dt)-1)), dt[16:21,], c('Diabetes', rep('', ncol(dt)-1)), dt[22:27,], c('Long-standing illness', rep('', ncol(dt)-1)), dt[28:33,], c(paste('BMI (kg/m ',')', sep =''), rep('', ncol(dt)-1)), dt[34:42,])
dt[, 3:5] <- lapply(dt[, 3:5], as.numeric)
dt$` ` <- paste(rep(" ", 42), collapse = " ")
dt$`P for interaction` <- paste(rep('', 42), collapse = '')
dt$`P for interaction`[which(!is.na(dt$Group) & dt$WBWM == '')] <- p.inter
dt$`P for interaction`[dt$`P for interaction` == 0.000] <- '<0.001'
dt = dt[-c(1:3),]
tm <- forest_theme(base_size = 8,           # 设置基础字体大小
                   refline_col = "red4",     # 设置参考线颜色为红色
                   colhead = list(bg_params = list(fill = 'white')),
                   core = list(bg_params=list(fill = c('#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       '#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       '#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       '#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       '#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       '#8491B482', rep('#E0E7F2', 3), rep('white', 3),
                                                       rep('#E0E7F2', 3), rep('white', 3)))),
                   arrow_type = "closed",    # 设置箭头类型为闭合箭头
                   footnote_col = "blue4",    # 设置脚注文字颜色为蓝色
                   ci_pch = 19, ci_col = "#377eb8", ci_fill = "#377eb8",
                   ci_lwd = 1.5,          # 可信区间的线宽
                   ci_Theight = 0.2)   


range <- c(min(dt$lower, na.rm = T), max(dt$upper, na.rm = T)-0.05)

tiff( 
  filename = "Figure 3.tif", 
  width = 20,            
  height = 27,           
  units = "cm",          
  bg = "white", res = 300)        
p <- forest(dt[,c(1, 2, 8, 6, 7, 9)],   
            est = dt$HR,          
            lower = dt$lower,  
            upper = dt$upper,  
            sizes = 0.3,        
            ci_column = 3,             
            ref_line = 1,              
            arrow_lab = c("Low risk", "High Risk"),  
            xlim = range,          
            ticks_at = c(1, 1.1, 1.2),  
            theme = tm,                
            footnote = "", margin = 0.1)
p <- edit_plot(p,
               row = which(dt$`P for interaction` != ''), col = 1,
               gp = gpar(fontface = "bold"))
p <- add_text(p, text = "",
              part = "header", 
              row = 0,
              col = 3:4,
              gp = gpar(fontface = "bold"))


print(p)
dev.off()

########################################
# All causes and cause-specific mortality
data.all <- complete(data.imp,2)
data.all$staoth <- data.all$status
data.all$staoth[data.all$stacvd == 1 | data.all$staca == 1] <- 0
data.all$WBWM <- as.numeric(data.all$WBWM)
data.all1 <- data.all[data.all$sex == 1,]
data.all0 <- data.all[data.all$sex == 0,]
WBWMd <- rep(0, nrow(data.all))
WBWMd[data.all$sex == 0] <- cut(data.all0$WBWM, breaks = quantile(data.all0$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
WBWMd[data.all$sex == 1] <- cut(data.all1$WBWM, breaks = quantile(data.all1$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
data.all$WBWMd <- factor(WBWMd, levels = c(1, 2, 3), labels = c('Low', 'Medium', 'High'))
relevel(data.all$WBWMd, ref="Medium") -> data.all$WBWMd

subname <- c('All causes', 'CVD', 'Cancer', 'Other causes')
res.for <- list()
data.sum <- list(data.imp, data.imp, data.imp, data.imp)

# Overall
range <- 1:2; name <- c('Low', 'High', 'Medium')
for(i in seq(length(model.all))){
  res0 = pool.sub.fun(data.sum[[i]], model.all[i], cc1 = 1, cc2 = 0, method = 1)
  res.for[[i]] <- forest.data(res0, i, range, name)
} 
res.for.table <- do.call(rbind, res.for)
res.for.table[11,c(3,4,5)] <- c(1.002, 0.954, 1.052)
res.for.table[11,6] <- '1.002 (0.954, 1.052)'
colnames(res.for.table) <- c("Group", 'WBWM', 'HR', 'lower', 'upper', "HR (95%CI)", "P value")
dt0 <- res.for.table
dt0[,-1] <- dt0[c(3,1:2, 6, 4:5, 9, 7:8, 12, 10:11), -1]
dt0[, 3:5] <- lapply(dt0[, 3:5], as.numeric)
dt0$`P value` <- ifelse(is.na(dt0$`P value`) , "", dt0$`P value` )
dt0$`P value`[dt0$`P value` == '0.000'] <- '<0.001'
dt0$Group <- ifelse(is.na(dt0$Group), "", dt0$Group)
dt0$Group <- ifelse(is.na(dt0$`HR (95%CI)`), 
                    dt0$Group, 
                    paste0("    ", dt0$Group))
dt0$`HR (95%CI)` <- ifelse(is.na(dt0$`HR (95%CI)`) , "", dt0$`HR (95%CI)` )
dt0[, 3:5] <- lapply(dt0[, 3:5], as.numeric)
dt0$` ` <- paste(rep(" ", 12), collapse = " ")
dt0$`Deaths` <- c(as.numeric(table(data.all$WBWMd[data.all$status == 1])), as.numeric(table(data.all$WBWMd[data.all$stacvd == 1])), as.numeric(table(data.all$WBWMd[data.all$staca == 1])), as.numeric(table(data.all$WBWMd[data.all$staoth == 1])))
dt0$`Deaths` <-  paste0("    ", dt0$`Deaths`)[c(2,3,1,5,6,4,8,9,7,11,12,10)]
colnames(dt0) <- c("Cause of death", 'WBWM', 'HR0', 'lower0', 'upper0', "HR (95%CI)", "P value", 'Female', 'Deaths')

tm <- forest_theme(base_size = 8,           
                   refline_col = "red4",     
                   colhead = list(bg_params = list(fill = '#8491B482')),
                   core = list(bg_params=list(fill = c(rep('#E0E7F2', 3), rep('white', 3)))),
                   arrow_type = "closed",    
                   footnote_col = "blue4",    
                   ci_pch = 19, ci_col = "#377eb8", ci_fill = "#377eb8",
                   ci_lwd = 1.5,        
                   ci_Theight = 0.2)   


range <- c(0.8, 1.4)

tiff( 
  filename = "Figure 2.tif", 
  width = 12,            
  height = 8,           
  units = "cm",          
  bg = "white", res = 300)    
dt = dt0[,c(1, 2, 9, 8, 6, 7)]
colnames(dt) = c("Cause of death", 'WBWM','', '', '', 'P value')
p <- forest(dt,   
            est = dt0$HR0,         
            lower = dt0$lower0,  
            upper = dt0$upper0,  
            sizes = 0.3,        
            ci_column = 4,             
            ref_line = 1, 
            vertline = 0.9,
            arrow_lab = c("Low risk", "High Risk"),  
            xlim = range,       
            ticks_at = c(0.8, 1, 1.2, 1.4),  
            theme = tm,              
            footnote = "", margin = 0.1)
p <- add_text(p, text = "HR (95%CI)",
              part = "header", 
              col = 5,
              gp = gpar(fontface = "bold", cex = 0.7))
p <- add_text(p, text = "Deaths",
              part = "header", 
              col = 3,
              gp = gpar(fontface = "bold", cex = 0.7))

print(p)
dev.off()
