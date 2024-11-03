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

# Data
setwd('~') 

# Functions we need
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

# pool.join.fun: function used to pool the estimates of M imputed datasets with joint model
# eg: pool.joinfunc(data, mod, method = 1)
pool.join.fun <- function(data, mod, cc, method){
  
  # data: data with M imputed datasets
  # mod: joint model
  # method: method used to pool the data
  
  if(method == 1){
    cond <- conds1[cc]
    Q_set <- NULL
    U_set <- list()
    M <- data$m
    
    for (i in 1:M) {
      data_i <- complete(data, i)
      data_i0 <- data_i[data_i$sex == 0, ]
      data_i1 <- data_i[data_i$sex == 1, ]
      data_i$wt.res[data_i$sex == 0] = lm(weight~WBWM, data = data_i0)$residuals
      data_i$wt.res[data_i$sex == 1] = lm(weight~WBWM, data = data_i1)$residuals
      data_i$height <- sqrt(data_i$weight/data_i$bmi)*100
      data_i$bmid = factor(cut(data_i$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity')))
      loct <- data_i$delta < 0
      deltad <- rep(0, nrow(data_i))
      q0 <- median(data_i$delta[data_i$sex == 0 & loct])
      q1 <- median(data_i$delta[data_i$sex == 1 & loct])
      deltad[data_i$sex == 0] <- cut(data_i0$delta, breaks = c(-Inf, q0, 0, Inf), include.lowest = T, right = F, labels = c('Decreasers', 'Stableers', 'Increasers'))
      deltad[data_i$sex == 1] <- cut(data_i1$delta, breaks = c(-Inf, q1, 0, Inf), include.lowest = T, right = F, labels = c('Decreasers', 'Stableers', 'Increasers'))
      data_i$deltad <- factor(deltad, levels = c(1, 2, 3), labels = c('Decreasers', 'Stableers', 'Increasers'))
      relevel(data_i$deltad, ref="Stableers") -> data_i$deltad
      inter <- paste(data_i$WBWMd, ', ', data_i$deltad, sep = '')
      data_i$inter <- as.factor(inter)
      relevel(data_i$inter, ref="Medium, Stableers") -> data_i$inter
      if(cond == 'All'){
        data.sub = data_i
      } else{
        data.sub <- data_i[eval(parse(text = cond)), ] 
      }
      fit_i <- coxph(formula = as.formula(mod), data = data.sub)
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
    fit <- with(data, coxph(formula = as.formula(mod)))
    res <- pool(fit)
  }
  return(res)
}

# sub.test: functions used to calculate P for interation
sub.test <- function(data, lm.mod, cox.mod){
  
  # data: data with M imputed datasets
  # lm.mod: linear model to calculate wt.res
  # cox.mod: model list include two models with or without interaction term
  cox.mod1 <- cox.mod[1]
  cox.mod2 <- cox.mod[2]
  cox1 <- with(data, {aged = factor(age)
  aged2 = cut(age, breaks = c(0, 65, 70), include.lowest = T)
  wt.res = lm(as.formula(lm.mod))$residuals
  coxph(formula = as.formula(cox.mod1))
  })
  cox2 <- with(data, {aged = factor(age)
  wt.res = lm(as.formula(lm.mod))$residuals
  coxph(formula = as.formula(cox.mod2))
  })
  res <- D2(cox1, cox2, use = 'likelihood')
  pval <- res$result[4]
  return(pval)
}


# Data
load('data.join.imp.RData')

# Overall
data.imp = data.join.imp
# Models
cox.mod = list(sprintf("Surv(time, status) ~ %s", paste(c('inter', 'age', 'sex', 'weight', 'height', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'sex', 'weight', 'height', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'weight', 'height', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'weight', 'height', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")))

cox.mod = list(sprintf("Surv(time, status) ~ %s", paste(c('inter', 'age', 'sex', 'bmid', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet', 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'sex', 'bmid', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'bmid', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")),
               sprintf("Surv(time, status) ~ %s", paste(c('WBWMd*deltad', 'age', 'bmid', 'edu', 'ethnic', 'TDI', 'smoke', 'alcohol', 'diet' , 'physical', 'longill', 'diabetes', 'hypertension', 'cancer', 'CVD', 'kidney'), collapse = " + ")))

conds1 <- c('All', 'data_i$sex == 1', 'data_i$sex == 0')

# Analysis
data.join <- complete(data.imp,2)
dim(data.join)

# All
res0 <- pool.join.fun(data.imp, cox.mod[[1]], cc = 1, method = 1)
res1 <- data.frame(expesy = sprintf("%.3f", res0$expest), lwr = sprintf("%.3f", res0$explwr), upr = sprintf("%.3f", res0$expupr))
res2 <- data.frame(expci = sprintf("%.3f (%.3f, %.3f)", res0$expest, res0$explwr, res0$expupr), pval = sprintf("%.3f", res0$p.value))
res <- rbind(c(rep(1,3), 'Reference', NA), cbind(res1, res2))[c(1, 8:9,7, 5:6 ,4, 2:3),]
res$`N` <- as.numeric(table(complete(data.imp,2)$inter)[c(1, 8:9, 7, 5:6 ,4, 2:3)])
res$`Deaths` <- as.numeric(table(data.join$inter[data.join$status == 1])[c(1, 8:9, 7, 5:6 ,4, 2:3)])
res$Group <- rep(c('Stable', 'Decrease', 'Increase'), 3)
res <- res[,c(ncol(res),(1:(ncol(res)-1)))]
res.all <- rbind(c(paste('Medium'), rep(NA, ncol(res)-1)), res[1:3,], c(paste('Low'), rep(NA, ncol(res)-1)), res[4:6,], c(paste('High'), rep(NA, ncol(res)-1)), res[7:9, ])
res.all[, 5:6] <- lapply(res.all[, 5:6], as.character)
colnames(res.all) <- c("Group", 'HR', 'lower', 'upper', "HR (95%CI)", "P value", "N", 'Deaths')
dt <- res.all
dt[, c(2:4)] <- lapply(dt[, c(2:4)], as.numeric)
dt$`P value` <- ifelse(is.na(dt$`P value`) , "", dt$`P value` )
dt$`P value`[dt$`P value` == '0.000'] <- '<0.001'
dt$Group <- ifelse(is.na(dt$`HR (95%CI)`), 
                   dt$Group, 
                   paste0("    ", dt$Group))
dt$`HR (95%CI)` <- ifelse(is.na(dt$`HR (95%CI)`) , "", dt$`HR (95%CI)` )
dt$`N` <- ifelse(is.na(dt$N) , "", dt$N )
dt$`Deaths` <- ifelse(is.na(dt$Deaths) , "", dt$Deaths)
dt$`Deaths` <-  paste0("    ", dt$`Deaths`)
dt$` ` <- paste(rep(" ", 12), collapse = " ")
tm <- forest_theme(base_size = 9,          
                   refline_col = "red4",    
                   colhead = list(bg_params = list(fill = '#8491B482')),
                   core = list(bg_params=list(fill = c('#E0E7F2', rep('white',3)))),
                   arrow_type = "closed",    
                   footnote_col = "blue4",  
                   ci_pch = 19, ci_col = "#377eb8", ci_fill = "#377eb8",
                   ci_lwd = 1.5,      
                   ci_Theight = 0.2)   
range <- c(min(dt$lower, na.rm = T)-0.5, max(dt$upper, na.rm = T)+0.5)
tiff( 
  filename = "Figure 4.tif", 
  width = 12,            
  height = 9.5,           
  units = "cm",          
  bg = "white", res = 600) 
p <- forest(dt[,c(1, 8, 9, 5, 6)],   
            est = dt$HR,        
            lower = dt$lower,  
            upper = dt$upper,  
            sizes = 0.3,        
            ci_column = 3,             
            ref_line = 1,              
            arrow_lab = c("Low risk", "High Risk"),  
            xlim = range,          
            ticks_at = c(1, 2, 3),  
            theme = tm,                
            footnote = "", main = 'Overall')  
p <- edit_plot(p,
               row = which(dt$`HR (95%CI)` == ""), col = 1,
               gp = gpar(fontface = "bold"))
print(p)
dev.off()


