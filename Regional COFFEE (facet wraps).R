# An implementation of COFFEE (COVID-19 Forecasts using Fast Evaluations and Estimation)
# By Lauren Castro, Geoffrey Fairchild, Isaac Michaud, and Dave Osthus @ Los Alamos National Laboratory
# Full paper available at: https://covid-19.bsvgateway.org/static/COFFEE-methodology.pdf
# R-code by Jakub Červený (jakub.cerveny@health.gov.sk), IZA MZSR
# Hospitalization data and estimates by Kristián Šufliarsky (kristian.sufliarsky@health.gov.sk), IZA MZSR
# We strongly encourage anyone interested to first study the original paper

library("data.table")
library("plyr")
library("boot")
library("dplyr")
library("gtools")
library("fastDummies")
library("ggplot2")
library("MASS")
library("COUNT")
library("foreach")
library("projections")
library("incidence")
library("zoo")

# Set system locale to EN/US due to english week days
# Windows: Sys.setlocale(category = "LC_ALL", locale = "English_United States.1252")
# *NIX: Sys.setlocale("LC_TIME", "en_US")

# define some constants/variables
data="https://raw.githubusercontent.com/Institut-Zdravotnych-Analyz/covid19-data/main/OpenData_Slovakia_Covid_DailyStats_Regions.csv"
# Forecast window size in days
K=30
# Nominal attack rate of covid-19
ar=0.55
# Share of people hospitalized, based on admissions data
hosp_share=0.061
# Share of people ventilated
vent_share=0.081
# Quantiles of prediction intervals
pred_int<-c(0.1, 0.25, 0.5, 0.75, 0.9)
colnames_int<-sapply(pred_int, function(x) paste("X", x, sep=""))
# Hospitalizations data
hosp_data="https://raw.githubusercontent.com/Institut-Zdravotnych-Analyz/covid19-data/main/OpenData_Slovakia_Covid_Hospital.csv"
# Folder to output graphs
output_folder="~/Documents/"

#### Functions
# Forecasting function
k_t_forecast <- function(eta,omega,phi)
{
  lambda = 1+k*((phi-1)/30)
  w<-rep(0, length(k))
  w[k<=omega+1] <- 1-((k[k<=omega+1]-1)/omega)^2
  eta_star = median_k_t*eta
  
  x<-cbind(eta_star, k_t_star_pred)
  
  forecast<-lambda*(w*apply(x, 1, min)+(1-w)*k_t_constant_dow)
  return(rev(forecast))
}

# Joint distribution function
joint_distr <- function (eta,omega,phi) {
  k_t_forecast<-k_t_forecast(eta,omega,phi)
  distance<-(inv.logit(k_t_forecast)-k_t)^2
  inv_distance=sum(distance)^-1
  distrib<-c(eta,omega,phi,inv_distance)
  return(distrib)
}

# Cases forecast function
forecast_cases<-function(int) {
  inv_k_t_forecast<-rev(inv.logit(int))
  
  for (row in K:1) {
    if (row == K) {
      d_c_forecast[row]<-inv_k_t_forecast[row]*(d_s_T/d_s0_forecast)*d_c_T
      d_c_dot_forecast[row]<-d_c_T+d_c_forecast[row]
      d_s_forecast[row]<-d_s_T-d_c_forecast[row]
    } else {
      d_c_forecast[row]<-inv_k_t_forecast[row]*(d_s_forecast[row+1]/d_s0_forecast)*
        d_c_dot_forecast[row+1]
      d_c_dot_forecast[row]<-d_c_dot_forecast[row+1]+d_c_forecast[row]
      d_s_forecast[row]<-d_s_forecast[row+1]-d_c_forecast[row]
    }
  }
  d_c_forecast<-round(d_c_forecast)
  params<-fitdist(d_c_forecast,distr="nbinom",method="mle")
  d_c_forecast<-sapply(d_c_forecast, function(x) rnbinom(1, mu=x, size=x/params$estimate[1]))
  return(d_c_forecast)
}  

# Prediction intervals function
get_quantiles<-function(qnt) {
  apply(cases_dist, 1, quantile, p=qnt)
}

# Function to simulate number of hospitalized people
# Based on https://cmmid-lshtm.shinyapps.io/hospital_bed_occupancy_projections/
# Assumes that each day a certain share of newly diagnosed cases ends up hospitalized
# The share is offset by 6 days forward
# For each case admitted on a particular day, LOS is drawn from a Weibull distribution with parameters estimated on real data
# All cases are then simulated over the forecast period
hospitalizations <- function(n_admissions, dates, r_los, n_sim = 10) {
  if (inherits(r_los, "distcrete")) {
    r_los <- r_los$r
  }
  
  admission_dates <- rep(dates, n_admissions)
  n <- length(admission_dates)
  last_date <- max(dates)
  out <- vector(n_sim, mode = "list")
  
  for (j in seq_len(n_sim)) {
    los <- r_los(n)
    list_dates_beds <- lapply(seq_len(n),
                              function(i) seq(admission_dates[i],
                                              length.out = los[i],
                                              by = 1L))
    dates_beds <- do.call(c, list_dates_beds)
    beds_days <- incidence::incidence(dates_beds)
    if (!is.null(last_date)) {
      to_keep <- incidence::get_dates(beds_days) <= last_date
      beds_days <- beds_days[to_keep, ]
    }
    
    out[[j]] <- projections::build_projections(
      x = beds_days$counts,
      dates = incidence::get_dates(beds_days))
  }
  projections::merge_projections(out)
}

# Simulate distribution of LOS, based on estimated empirical fit
los_h <- distcrete::distcrete("weibull", shape = 1.36, scale = 10.3, w = 0, interval = 1)
los_v <- distcrete::distcrete("weibull", shape = 1.32, scale = 10.984, w = 0, interval = 1)

####

# Initialize data
hospitalized_data<-read.csv(url(hosp_data), header = TRUE, sep=";")
hospitalized_data$date <- as.Date(hospitalized_data$Datum)

ventilated_data <- hospitalized_data %>% group_by(Kraj, date) %>% summarise_(ventilated="sum(Plucna_vent_lozka)")
hospitalized_data <- hospitalized_data %>% group_by(Kraj, date) %>% summarise_(hospitalized="sum(hospitalizovany)")

ventilated_data<-ventilated_data[seq(dim(ventilated_data)[1],1),]
hospitalized_data<-hospitalized_data[seq(dim(hospitalized_data)[1],1),]

cases_data<-read.csv(url(data), header = TRUE, sep=";")
cases_data$date <- as.Date(cases_data$date)

region<-c(unique(cases_data$Region))
options(encoding = "UTF-8")

# Initialize lists for csv output
cases_summary = list()
hosp_summary = list()
vent_summary = list()

# Loop over regions

for (reg in region) {
  
  # Population  
  if (reg == "Banskobystrický kraj") {
    pop = 645276
  }  else if (reg == "Bratislavský kraj") {
    pop = 659598
  } else if (reg == "Košický kraj") {
    pop = 801460
  } else if (reg == "Nitriansky kraj") {
    pop = 674306
  } else if (reg == "Prešovský kraj") {
    pop = 826244
  } else if (reg == "Trenčiansky kraj") {
    pop = 589935
  } else if (reg == "Trnavský kraj") {
    pop = 564917
  } else if (reg == "Žilinský kraj") {
    pop = 691509
  }
  
  # Subset data
  hospital_data<-as.data.frame(subset(hospitalized_data, Kraj==reg))
  covid_data<-subset(cases_data, Region==reg)
  vent_data<-as.data.frame(subset(ventilated_data, Kraj==reg))
  
  # Generate k_t, tau_c
  covid_data$k_t=(covid_data$positive/lead(covid_data$positive))-1
  covid_data[nrow(covid_data), "k_t"]<-0
  tau_c=0.95*min(covid_data$k_t[covid_data$k_t > 0])
  # Generate k_t_star
  covid_data$k_t_star[covid_data$k_t > tau_c & covid_data$k_t < 1-tau_c]<-logit(covid_data$k_t[covid_data$k_t > tau_c & covid_data$k_t < 1-tau_c])
  covid_data$k_t_star[covid_data$k_t <= tau_c]<-logit(tau_c)
  covid_data$k_t_star[covid_data$k_t >= 1-tau_c]<-logit(1-tau_c)
  # Generate day of week
  covid_data$wday=as.POSIXlt(covid_data$date)$wday
  covid_data$day <- weekdays(as.Date(covid_data$date))
  # Generate dummies
  covid_data <- fastDummies::dummy_cols(covid_data, select_columns = "day")
  # Linear trend
  covid_data$n <- rev(seq.int(nrow(covid_data)))
  
  # Subset last 42 observations
  last42 <-head(subset(covid_data, select=c("date", "positive", "newcases", "k_t", "k_t_star", "n", "day_Friday", "day_Monday", "day_Saturday",
                                            "day_Sunday", "day_Thursday", "day_Tuesday", "day_Wednesday")), 42)
  
  # Subset training data
  training <-subset(last42[15:42,], select=c("date", "positive", "newcases", "k_t", "k_t_star", "n", "day_Friday", "day_Monday", "day_Saturday",
                                             "day_Sunday", "day_Thursday", "day_Tuesday", "day_Wednesday"))
  
  # Subset test data
  test <-subset(last42[1:14,], select=c("date", "positive", "newcases", "k_t", "k_t_star", "n", "day_Friday", "day_Monday", "day_Saturday",
                                        "day_Sunday", "day_Thursday", "day_Tuesday", "day_Wednesday"))
  
  # Estimate regression
  model<-lm(k_t_star ~ n + day_Monday + day_Tuesday + day_Wednesday + day_Thursday + day_Friday + day_Saturday,
            data=training)
  summary(model)
  # Include Cook's distance
  training$cookd = cooks = cooks.distance(model)
  
  # Inverse of Cook's distance
  training$invcookd = training$cookd^-1
  # Weighted regression
  weighted_model<-lm(k_t_star ~ n + day_Monday + day_Tuesday + day_Wednesday + day_Thursday + day_Friday + day_Saturday,
                     data=training, weights=training$invcookd)
  summary(weighted_model)
  
  # Predict fitted values
  training$k_t_star_pred=predict(weighted_model)
  test$k_t_star_pred=predict(weighted_model, newdata = test)
  
  # Plot
  p <- ggplot() +
    # Last 42 days
    geom_point(data=last42, aes(x=date, y=k_t_star)) +
    geom_line(data=training, aes(x=date, y=k_t_star_pred)) +
    # Predicted 14 days of test window
    geom_line(data=test, aes(x=date, y=k_t_star_pred))
  
  # Average number of daily cases reported over the last week of the training window
  y_ct_avg<-sum(last42$newcases[15:21])/7
  
  last42$k_t_constant=logit(y_ct_avg*(((ar*pop-lead(last42$positive))/(ar*pop))*lead(last42$positive))^-1)
  test$k_t_constant=logit(y_ct_avg*(((ar*pop-lead(test$positive))/(ar*pop))*lead(test$positive))^-1)
  test[14, 'k_t_constant']=logit(y_ct_avg*(((ar*pop-last42[15, 'positive'])/(ar*pop))*last42[15, 'positive'])^-1)
  
  # Compute k_t_constant + DOW
  foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
    day=paste("day_",d,sep="")
    if (d == "Sunday") {
      last42$k_t_constant_dow[last42[, day] == 1] <- last42$k_t_constant[last42[, day] == 1]
    } else {
      last42$k_t_constant_dow[last42[, day] == 1] <- last42$k_t_constant[last42[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
    }
  }
  
  last42$k_t_constant_dow<-last42$k_t_constant_dow-(mean(last42$k_t_constant_dow)-mean(last42$k_t_constant))
  
  # Compute k_t_constant + DOW
  foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
    day=paste("day_",d,sep="")
    if (d == "Sunday") {
      test$k_t_constant_dow[test[, day] == 1] <- test$k_t_constant[test[, day] == 1]
    } else {
      test$k_t_constant_dow[test[, day] == 1] <- test$k_t_constant[test[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
    }
  }
  
  test$k_t_constant_dow<-test$k_t_constant_dow-(mean(test$k_t_constant_dow)-mean(test$k_t_constant))
  
  # Plot
  p <- ggplot() +
    # Last 42 days
    geom_point(data=last42, aes(x=date, y=k_t_star)) +
    # Predicted 14 days of test window
    geom_line(data=test, aes(x=date, y=k_t_constant))
  
  last42$k<- seq(14, length.out=nrow(last42), by=-1)
  test$k<- seq(14, length.out=nrow(test), by=-1)
  
  median_k_t<-median(as.vector(training$k_t_star_pred[1:7]))
  
  # Generate a grid of parameters for the joint distribution
  seq_phi<-seq(0.90, 1.10, by=0.01)
  seq_omega<-seq(1, 60, by=1)
  seq_eta<-cbind(0.25, 0.4375, 0.625, 0.8125, 1)
  complete_dist<-expand.grid(seq_eta, seq_omega, seq_phi)
  complete_dist<-as.matrix(complete_dist)
  
  # Initialize vectors
  k<-test$k
  k_t_star_pred<-test$k_t_star_pred
  k_t_constant_dow<-test$k_t_constant_dow
  k_t<-test$k_t
  
  distr<-mapply(joint_distr,complete_dist[,1],complete_dist[,2],complete_dist[,3])
  distr<-t(distr)
  distr<-cbind(distr, distr[,4]/sum(distr[,4]))
  distr<-distr[order(-distr[,5]),]
  
  # Forecast on test window
  test$k_t_forecast<-k_t_forecast(distr[1,1],distr[1,2],distr[1,3])
  
  p <- ggplot() +
    # Last 42 days
    geom_point(data=last42, aes(x=date, y=k_t_star)) +
    geom_line(data=last42, aes(x=date, y=k_t_star)) +
    # Predicted 14 days of test window
    geom_line(data=test, aes(x=date, y=k_t_forecast), linetype="dashed")
  
  ####
  # True forecast
  # Subsetnew training data
  new_training <-subset(last42[1:27,], select=c("date", "positive", "k_t", "k_t_star", "n", "day_Friday", "day_Monday", "day_Saturday",
                                                "day_Sunday", "day_Thursday", "day_Tuesday", "day_Wednesday"))
  
  # Create new prediction frame
  forecast<-data.frame(date=rev(seq(as.Date(new_training[1, "date"]+1), by="day", length.out=K, origin = "1970-01-01")))
  # Generate day of week
  forecast$wday=as.POSIXlt(forecast$date)$wday
  forecast$day <- weekdays(as.Date(forecast$date))
  # Generate dummies
  forecast <- fastDummies::dummy_cols(forecast, select_columns = "day")
  # Linear trend
  forecast$n <- rev(seq.int(new_training[1, "n"]+1,new_training[1, "n"]+nrow(forecast)))
  
  # Estimate regression
  model<-lm(k_t_star ~ n + day_Monday + day_Tuesday + day_Wednesday + day_Thursday + day_Friday + day_Saturday,
            data=new_training)
  summary(model)
  # Include Cook's distance
  new_training$cookd = cooks = cooks.distance(model)
  
  # Inverse of Cook's distance
  new_training$invcookd = new_training$cookd^-1
  # Weighted regression
  weighted_model<-lm(k_t_star ~ n + day_Monday + day_Tuesday + day_Wednesday + day_Thursday + day_Friday + day_Saturday,
                     data=new_training, weights=new_training$invcookd)
  summary(weighted_model)
  
  # Predict fitted values
  new_training$k_t_star_pred=predict(weighted_model)
  forecast$k_t_star_pred=predict(weighted_model, newdata = forecast)
  
  # Number of new daily cases
  new_training$newcases=new_training$positive-lead(new_training$positive)
  
  # Average number of daily cases reported over the last week of the training window
  y_ct_avg_forecast<-sum(new_training$newcases[1:7])/7
  
  # Fit k_t_constant trajectory for the forecasting data
  k_t_trajectory<-head(subset(new_training, select=c("date", "positive", "n")), 14)
  
  k_t_trajectory$k_t_constant<-logit(y_ct_avg_forecast*(((ar*pop-lead(k_t_trajectory$positive))/(ar*pop))*lead(k_t_trajectory$positive))^-1)
  k_t_trajectory[14, "k_t_constant"]<-logit(y_ct_avg_forecast*(((ar*pop-k_t_trajectory[14, "positive"])/(ar*pop))*new_training[15, "positive"])^-1)
  k_t_cons_pred<-lm(k_t_constant ~ n, data=k_t_trajectory)
  forecast$k_t_constant=predict(k_t_cons_pred, newdata = forecast)
  
  # Compute k_t_constant + DOW
  foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
    day=paste("day_",d,sep="")
    if (d == 'Sunday') {
      forecast$k_t_constant_dow[forecast[, day] == 1] <- forecast$k_t_constant[forecast[, day] == 1]
    } else {
      forecast$k_t_constant_dow[forecast[, day] == 1] <- forecast$k_t_constant[forecast[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
    }
  }
  
  forecast$k_t_constant_dow<-forecast$k_t_constant_dow-(mean(forecast$k_t_constant_dow)-mean(forecast$k_t_constant))
  
  # Plot
  p <- ggplot() +
    # Last 27 days
    geom_point(data=new_training, aes(x=date, y=k_t_star)) +
    geom_line(data=new_training, aes(x=date, y=k_t_star_pred)) +
    # Predicted 14 days of test window
    geom_line(data=forecast, aes(x=date, y=k_t_star_pred))+
    geom_line(data=forecast, aes(x=date, y=k_t_constant))
  
  median_k_t<-median(as.vector(new_training$k_t_star_pred[1:7]))
  forecast$k<- seq(K, length.out=nrow(forecast), by=-1)
  
  # Initialize vectors for forecast
  d_s0_forecast=runif(1,0.4,0.7)*pop
  d_c_T<-new_training[1,2]
  d_s_T=d_s0_forecast-d_c_T
  d_c_forecast<-rep(0, K)
  d_c_dot_forecast<-rep(0, K)
  d_s_forecast<-rep(0, K)
  
  k<-forecast$k
  k_t_star_pred<-forecast$k_t_star_pred
  k_t_constant_dow<-forecast$k_t_constant_dow
  
  # Forecast
  if (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27) {
    forecast$X0.5<-rbinom(K,1,1/28)
  } else if (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14) {
    forecast$X0.5<-sample(new_training$newcases, K, replace = TRUE)
  } else {
    # Generate samples from the joint distribution
    sampled_dist<-distr[sample(nrow(distr), 2000, prob=distr[, 5], replace = TRUE), 1:3]
    
    # Forecast the joint distribution
    forecast_dist<-mapply(k_t_forecast,sampled_dist[,1],sampled_dist[,2],sampled_dist[,3])
    
    # Forecast the cases
    cases_dist<-apply(forecast_dist, 2, forecast_cases)
    
    cases_list<-lapply(pred_int, get_quantiles)
    names(cases_list) <- pred_int
    if ("X0.5" %in% colnames(forecast)) {
      forecast <- forecast[, ! names(forecast) %in% colnames_int, drop = F]
    }
    
    forecast<-cbind(forecast, as.data.frame(cases_list))
  }
  
  # Create sheet
  cases_summary[[reg]]<-rbind.fill(forecast[, names(forecast) %in% c("date", colnames_int)], last42[, names(last42) %in% c("date", "newcases")])
  
  # Forecast hospitalizations
  # Initialize the forecast with the current number of hospitalized
  current_beds=hospital_data$hospitalized[date=which.max(hospital_data$date)]
  
  forecast_hosp<-forecast[, names(forecast) %in% c("date", colnames_int)]
  
  forecast_hosp[,2:ncol(forecast_hosp)]<-forecast_hosp[,2:ncol(forecast_hosp)]*hosp_share
  forecast_hosp[K,2:ncol(forecast_hosp)]<-current_beds
  forecast_hosp[(K-1):(K-7),2:ncol(forecast_hosp)]<-forecast_hosp[(K-1):(K-7),2:ncol(forecast_hosp)]*0.8
  
  hosp_list<-lapply(forecast_hosp[,2:ncol(forecast_hosp)], hospitalizations, forecast_hosp[,1], los_h, 30)
  
  if ("X0.5" %in% colnames(forecast_hosp)) {
    forecast_hosp <- forecast_hosp[, ! names(forecast_hosp) %in% colnames_int, drop = F]
  }
  forecast_hosp<-cbind(forecast_hosp, sapply(names(hosp_list), function(x) apply(hosp_list[[x]], 1, stats::quantile, probs=as.numeric(substring(x,2)))))
  forecast_hosp[,2:ncol(forecast_hosp)]<-forecast_hosp[dim(forecast_hosp[,2:ncol(forecast_hosp)])[1]:1,2:ncol(forecast_hosp)]
  row.names(forecast_hosp) <- NULL
  
  # Smoothing of the prediction
  smoothing<-loess(formula = X0.5 ~ as.numeric(date), data=forecast_hosp, span=0.5)
  forecast_hosp$X0.5<-predict(smoothing)
  if (! (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27 | sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14)) {
    smoothing<-loess(formula = X0.1 ~ as.numeric(date), data=forecast_hosp, span=0.5)
    forecast_hosp$X0.1<-predict(smoothing)
    smoothing<-loess(formula = X0.25 ~ as.numeric(date), data=forecast_hosp, span=0.5)
    forecast_hosp$X0.25<-predict(smoothing)
    smoothing<-loess(formula = X0.75 ~ as.numeric(date), data=forecast_hosp, span=0.5)
    forecast_hosp$X0.75<-predict(smoothing)
    smoothing<-loess(formula = X0.9 ~ as.numeric(date), data=forecast_hosp, span=0.5)
    forecast_hosp$X0.9<-predict(smoothing)
  }
  
  # Create sheet
  hosp_summary[[reg]]<-rbind.fill(forecast_hosp, hospital_data[1:42, names(hospital_data) %in% c("date", "hospitalized")])
  
  # Forecast ICU ventilated
  current_vent=vent_data$ventilated[date=which.max(vent_data$date)]
  
  forecast_vent<-forecast[, names(forecast) %in% c("date", colnames_int)]
  
  forecast_vent[,2:ncol(forecast_vent)]<-forecast_vent[,2:ncol(forecast_vent)]*hosp_share*vent_share
  forecast_vent[K,2:ncol(forecast_vent)]<-current_vent
  forecast_vent[(K-1):(K-7),2:ncol(forecast_vent)]<-forecast_vent[(K-1):(K-7),2:ncol(forecast_vent)]*0.8
  
  vent_list<-lapply(forecast_vent[,2:ncol(forecast_vent)], hospitalizations, forecast_vent[,1], los_v, 30)
  
  if ("X0.5" %in% colnames(forecast_vent)) {
    forecast_vent <- forecast_vent[, ! names(forecast_vent) %in% colnames_int, drop = F]
  }
  forecast_vent<-cbind(forecast_vent, sapply(names(vent_list), function(x) apply(vent_list[[x]], 1, stats::quantile, probs=as.numeric(substring(x,2)))))
  forecast_vent[,2:ncol(forecast_vent)]<-forecast_vent[dim(forecast_vent[,2:ncol(forecast_vent)])[1]:1,2:ncol(forecast_vent)]
  row.names(forecast_vent) <- NULL
  
  # Smoothing of the prediction
  smoothing<-loess(formula = X0.5 ~ as.numeric(date), data=forecast_vent, span=0.5)
  forecast_vent$X0.5<-predict(smoothing)
  if (! (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27 | sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14)) {
    smoothing<-loess(formula = X0.1 ~ as.numeric(date), data=forecast_vent, span=0.5)
    forecast_vent$X0.1<-predict(smoothing)
    smoothing<-loess(formula = X0.25 ~ as.numeric(date), data=forecast_vent, span=0.5)
    forecast_vent$X0.25<-predict(smoothing)
    smoothing<-loess(formula = X0.75 ~ as.numeric(date), data=forecast_vent, span=0.5)
    forecast_vent$X0.75<-predict(smoothing)
    smoothing<-loess(formula = X0.9 ~ as.numeric(date), data=forecast_vent, span=0.5)
    forecast_vent$X0.9<-predict(smoothing)
  }
  
  # Create sheet
  vent_summary[[reg]]<-rbind.fill(forecast_vent, vent_data[1:42, names(vent_data) %in% c("date", "ventilated")])
  
}

cases_sheet<-rbindlist(cases_summary, fill=TRUE, idcol="region")
hosp_sheet<-rbindlist(hosp_summary, fill=TRUE, idcol="region")
vent_sheet<-rbindlist(vent_summary, fill=TRUE, idcol="region")

# Facet wrap plots
# Cases
colors_c <- c("Median" = "black", "80% prediction interval" = "deeppink", "50% prediction interval" = "hotpink3")

p <- ggplot() +
  # Real data
  geom_line(data=cases_sheet, aes(x=date, y=newcases), colour="gray78")+
  geom_point(data=cases_sheet, aes(x=date, y=newcases), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(new_training$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks")+xlab("Date")+ylab("Daily new cases")+scale_y_continuous(labels = scales::comma)

plot_intervals <- function(point = FALSE){
  list(
    if ("X0.9" %in% colnames(cases_sheet)) 
      geom_ribbon(data=cases_sheet, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
    geom_ribbon(data=cases_sheet, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
  )
}

p+plot_intervals()+scale_color_manual(values = colors_c)+scale_fill_manual(values = colors_c)+
  geom_line(data=cases_sheet, aes(x=date, y=X0.5, colour="Median"), size=1)+
  facet_wrap(~ region, scales="free_y", ncol=2)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.position="none" ,plot.title = element_text(hjust = 0.5))

ggsave("Cases.png",
       plot = last_plot(), device = "png",
       path = output_folder,
       dpi = 300
)

# Hospitalizations
colors_h <- c("Median" = "black", "80% prediction interval" = "darkorchid1", "50% prediction interval" = "darkorchid4")

p <- ggplot() +
  geom_line(data=hosp_sheet, aes(x=date, y=hospitalized), colour="gray78")+
  geom_point(data=hosp_sheet, aes(x=date, y=hospitalized), shape=21, colour="black", fill="darkorchid4", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(hospital_data$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks")+xlab("Date")+ylab("Hospitalized")+scale_y_continuous(labels = scales::comma)

plot_intervals_h <- function(point = FALSE){
  list(
    if ("X0.9" %in% colnames(hosp_sheet)) 
      geom_ribbon(data=hosp_sheet, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
    geom_ribbon(data=hosp_sheet, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
  )
}

p+plot_intervals_h()+scale_color_manual(values = colors_h)+scale_fill_manual(values = colors_h)+
  geom_line(data=hosp_sheet, aes(x=date, y=X0.5, colour="Median"), size=1)+
  facet_wrap(~ region, scales="free_y", ncol=2)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.position="none" ,plot.title = element_text(hjust = 0.5))

ggsave("Hospitalizations.png",
       plot = last_plot(), device = "png",
       path = output_folder,
       dpi = 300
)

# Ventilated
colors_v <- c("Median" = "black", "80% prediction interval" = "steelblue1", "50% prediction interval" = "steelblue4")

p <- ggplot() +
  geom_line(data=vent_sheet, aes(x=date, y=ventilated), colour="gray78")+
  geom_point(data=vent_sheet, aes(x=date, y=ventilated), shape=21, colour="black", fill="steelblue4", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(vent_data$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks")+xlab("Date")+ylab("Ventilated")+scale_y_continuous(labels = scales::comma)

plot_intervals_v <- function(point = FALSE){
  list(
    if ("X0.9" %in% colnames(vent_sheet)) 
      geom_ribbon(data=vent_sheet, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
    geom_ribbon(data=vent_sheet, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
  )
}

p+plot_intervals_v()+scale_color_manual(values = colors_v)+scale_fill_manual(values = colors_v)+
  geom_line(data=vent_sheet, aes(x=date, y=X0.5, colour="Median"), size=1)+
  facet_wrap(~ region, scales="free_y", ncol=2)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.position="none" ,plot.title = element_text(hjust = 0.5))

ggsave("Ventilated.png",
       plot = last_plot(), device = "png",
       path = output_folder,
       dpi = 300
)

write.csv(hosp_sheet, file = paste(output_folder,"Hospitalizations.csv",sep=""), )
write.csv(vent_sheet, file = paste(output_folder,"ICU ventilated.csv",sep=""), )
write.csv(cases_sheet, file = paste(output_folder,"Cases.csv",sep=""), )
