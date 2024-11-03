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
load('data.join.RData')

# Functions
# pool.fun.sub: function used to pool the estimates with subgroups of M imputed datasets
# eg: pool.func(data, mod1, sub, cc = 2, method = 1)
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
      data_i$bmid = factor(cut(data_i$bmi, breaks = c(-Inf, 18.5, 25, 30, Inf), labels = c('Underweight', 'Normal weight', 'Overweight', 'Obesity')))
      data_i0 <- data_i[data_i$sex == 0, ]
      data_i1 <- data_i[data_i$sex == 1, ]
      WBWMd <- rep(0, nrow(data_i))
      WBWMd[data_i$sex == 0] <- cut(data_i0$WBWM, breaks = quantile(data_i0$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      WBWMd[data_i$sex == 1] <- cut(data_i1$WBWM, breaks = quantile(data_i1$WBWM, c(0, 1/3, 2/3, 1)), include.lowest = T, right = F, labels = c('Low', 'Medium', 'High'))
      data_i$WBWMd <- factor(WBWMd, levels = c(1, 2, 3), labels = c('Low', 'Medium', 'High'))
      relevel(data_i$WBWMd, ref="Medium") -> data_i$WBWMd
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
      data_i0 <- data_i[data_i$sex == 0, ]
      data_i1 <- data_i[data_i$sex == 1, ]
      data_i$wt.res[data_i$sex == 0] = lm(weight~WBWM, data = data_i0)$residuals
      data_i$wt.res[data_i$sex == 1] = lm(weight~WBWM, data = data_i1)$residuals
      data_i$height <- sqrt(data_i$weight/data_i$bmi)*100
      if(cond == 'All'){
        data.sub = data_i
      } else{
        data.sub <- data_i[eval(parse(text = cond)), ] 
      }
      fit_i <- coxph(formula = as.formula(mod), data = data.sub)
      #rint(cox.zph(fit_i, transform = 'rank'))
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

model.all <- c('Surv(time, status) ~ deltad + WBWMd + sex + age + wt.res + height + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, stacvd) ~ deltad + WBWMd + sex + age + wt.res + height + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, staca) ~ deltad + WBWMd + sex + age + wt.res + height + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, stares) ~ deltad + WBWMd + sex + age + wt.res + height + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, stadig) ~ deltad + WBWMd + sex + age + wt.res + height + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney')
model.all <- c('Surv(time, status) ~ deltad + WBWMd + sex + age + bmid + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, stacvd) ~ deltad + WBWMd + sex + age + bmid + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, staca) ~ deltad + WBWMd + sex + age + bmid + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney',
               'Surv(time, staoth) ~ deltad + WBWMd + sex + age + bmid + edu + ethnic + TDI + smoke + alcohol + diet + physical + longill + diabetes + hypertension + CVD + cancer + kidney')
conds1 <- c('All', 'data_i$sex == 0', 'data_i$sex == 1')

########################################
# all-cause and cause-specific mortality
data.imp = data.join.imp
data.all <- complete(data.imp,2)
data.all$staoth = data.all$status
data.all$staoth[data.all$staca == 1 | data.all$stacvd == 1] <- 0
subname <- c('All causes', 'CVD', 'Cancer', 'Other causes')
res.for <- list()
#data.sum <- list(data.imp, data.cvd, data.ca, data.res, data.dig)
data.sum <- list(data.imp, data.imp, data.imp, data.imp)
range <- 1:2; name <- c('Decrease', 'Increase', 'Stable')
for(i in seq(length(model.all))){
  res0 = pool.sub.fun(data.sum[[i]], model.all[i], cc = 1, method = 1)
  res.for[[i]] <- forest.data(res0, i, range, name)
} 
res.for.table <- do.call(rbind, res.for)
colnames(res.for.table) <- c("Group", 'WBWM', 'HR', 'lower', 'upper', "HR (95%CI)", "P value")
dt <- res.for.table
dt[,-1] <- dt[c(3,1:2, 6, 4:5, 9, 7:8, 12, 10:11), -1]
dt[, 3:5] <- lapply(dt[, 3:5], as.numeric)
dt$`P value` <- ifelse(is.na(dt$`P value`) , "", dt$`P value` )
dt$`P value`[dt$`P value` == '0.000'] <- '<0.001'
dt$Group <- ifelse(is.na(dt$Group), "", dt$Group)
dt$Group <- ifelse(is.na(dt$`HR (95%CI)`), 
                   dt$Group, 
                   paste0("    ", dt$Group))
dt$`HR (95%CI)` <- ifelse(is.na(dt$`HR (95%CI)`) , "", dt$`HR (95%CI)` )
#dt <- rbind(dt[1:3,], c('Sex', rep('', ncol(dt)-1)), dt[4:9,], c('Age', rep('', ncol(dt)-1)), dt[10:15,], c('Ethnicity', rep('', ncol(dt)-1)), dt[16:21,], c('Long-illness', rep('', ncol(dt)-1)), dt[22:27,])
dt[, 3:5] <- lapply(dt[, 3:5], as.numeric)
dt$` ` <- paste(rep(" ", 12), collapse = " ")
#res$`N` <- as.numeric(table(complete(data.imp,2)$inter)[c(1, 8:9, 7, 5:6 ,4, 2:3)])
#dt$`Deaths` <- dt$Group
dt$`Deaths` <- c(as.numeric(table(data.all$WBWMd[data.all$status == 1])), as.numeric(table(data.all$WBWMd[data.all$stacvd == 1])), as.numeric(table(data.all$WBWMd[data.all$staca == 1])), as.numeric(table(data.all$WBWMd[data.all$staoth == 1])))
dt$`Deaths` <-  paste0("    ", dt$`Deaths`)[c(2,3,1,5,6,4,8,9,7,11,12,10)]
#dt$`P for interaction` <- paste(rep('', 24), collapse = '')
#dt$`P for interaction`[which(!is.na(dt$Group) & dt$WBWM == '')] <- p.inter
colnames(dt) <- c("Cause of death", expression(paste(Delta, 'WBWM', sep ='')), 'HR', 'lower', 'upper', "HR (95%CI)", "P value", 'Overall', 'Deaths')


range <- 3:4; name <- c('Low', 'High', 'Medium')
for(i in seq(length(model.all))){
  res0 = pool.sub.fun(data.sum[[i]], model.all[i], cc = 1, method = 1)
  res.for[[i]] <- forest.data(res0, i, range, name)
} 
res.for.table <- do.call(rbind, res.for)
colnames(res.for.table) <- c("Group", 'WBWM', 'HR', 'lower', 'upper', "HR (95%CI)", "P value")
dt0 <- res.for.table
dt0[, 3:5] <- lapply(dt0[, 3:5], as.numeric)
dt0$`P value` <- ifelse(is.na(dt0$`P value`) , "", dt0$`P value` )
dt$`P value`[dt$`P value` == '0.000'] <- '<0.001'
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

range <- c(min(dt$lower, na.rm = T)-0.1, max(dt$upper, na.rm = T)-0.2)
dt.all <- cbind(dt0, dt)
tm <- forest_theme(base_size = 8,          
                   refline_col = "red4",     
                   colhead = list(bg_params = list(fill = '#8491B482')),
                   core = list(bg_params=list(fill = c(rep('#E0E7F2', 3), rep('white', 3)))),
                   arrow_type = "closed",   
                   footnote_col = "blue4",    
                   ci_pch = 19, ci_col = "#377eb8", ci_fill = "#377eb8",
                   ci_lwd = 1.5,         
                   ci_Theight = 0.2)   

range <- c(min(dt$lower, na.rm = T)-0.1, 2.2)
range <- c(0.6, 2.2)
setwd('F:\\2024\\UK biobank\\Mortality & WBWM\\results7')

tiff( 
  filename = "Supplementary Figure 2.tif", 
  width = 10.5,            
  height = 8.5,           
  units = "cm",          
  bg = "white", res = 300)    
dt.sum = dt.all[,c(1, 11, 17, 15, 16)]
colnames(dt.sum) = c("Cause of death", '', '', '', 'P value')
p <- forest(dt.sum,  
            est = list(dt.all$HR),         
            lower = list(dt.all$lower),  
            upper = list(dt.all$upper),  
            sizes = 0.3,        
            ci_column = c(3),             
            ref_line = 1, 
            vertline = 0.9,
            arrow_lab = c("Low risk", "High Risk"),  
            xlim = range,         
            ticks_at = c(0.6, 1, 1.4, 1.8, 2.2),  
            theme = tm,                
            footnote = "", margin = 0.1)
p <- add_text(p, text = "HR (95%CI)",
              part = "header", 
              col = 4,
              gp = gpar(fontface = "bold", cex = 0.7))
p <- add_text(p, text = expression(paste(Delta, 'WBWM', sep='')),
              part = "header", 
              col = 2,
              gp = gpar(fontface = "bold", cex = 0.7))
p <- add_text(p, text = expression(paste(Delta, 'WBWM', sep='')),
              part = "header", 
              col = 2,
              gp = gpar(fontface = "bold", cex = 0.7))

print(p)
dev.off()

