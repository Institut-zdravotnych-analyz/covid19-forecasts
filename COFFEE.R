# An implementation of COFFEE (COVID-19 Forecasts using Fast Evaluations and Estimation)
# By Lauren Castro, Geoffrey Fairchild, Isaac Michaud, and Dave Osthus @ Los Alamos National Laboratory
# Full paper available at: https://covid-19.bsvgateway.org/static/COFFEE-methodology.pdf
# R-code by Jakub Červený (jakub.cerveny@health.gov.sk), IZA MZSR
# Hospitalization data and estimates by Kristián Šufliarsky (kristian.sufliarsky@health.gov.sk), IZA MZSR
# We strongly encourage anyone interested to first study the original paper

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

# Set system locale to EN/US due to english week days
# Windows: Sys.setlocale(category = "LC_ALL", locale = "English_United States.1252")
# *NIX: Sys.setlocale("LC_TIME", "en_US")

# Define some constants/variables
data="https://mapa.covid.chat/export/csv"
# population of the forecasted area
pop=5500000
# Forecast window size in days
K=27
# Nominal attack rate of covid-19
ar=0.55
# Share of people hospitalized, based on admissions data
hosp_share=0.067
# Eta parameter definitions for different scenarios
best=1.05
mid=1
worst=0.9
# Folder to output graphs
output_folder="~/Documents/COFFEE Covid forecasts/"

# Simulate distribution of LOS, based on estimated empirical fit
los <- distcrete::distcrete("weibull", shape = 1.36, scale = 12, w = 0, interval = 1)

#### Functions
# Forecasting function
k_t_forecast <- function(eta,omega,phi,dframe)
{
  forecast<-c()
  for (row in 1:nrow(dframe)) {
    k<-dframe[row, "k"]
    k_t_star_pred<-dframe[row, "k_t_star_pred"]
    k_t_constant_dow<-dframe[row, "k_t_constant_dow"]
    
    lambda = 1+k*((phi-1)/30)
    w = if (k<=omega+1) {
      1-((k-1)/omega)^2
    } else { w = 0 }
    eta_star = median_k_t*eta
    
    x<-c(eta_star, k_t_star_pred)
    
    forecast<-c((lambda*(w*min(x)+(1-w)*k_t_constant_dow)), forecast)
  }
  return(forecast)
}

# Joint distribution function
joint_dist <- function (eta,omega,phi) {
  test$kt_forecast<-rev(k_t_forecast(eta,omega,phi,test))
  test$dist=(inv.logit(test$kt_forecast)-test$k_t)^2
  inv_dist=sum(test$dist)^-1
  dist<-c(eta,omega,phi,inv_dist)
  return(dist)
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

####

covid_data<-read.csv(url(data), header = TRUE, sep=";")
covid_data<-covid_data[seq(dim(covid_data)[1],1),]
covid_data$date <- as.Date(covid_data$Datum, format = "%d-%m-%Y")
# Rename columns manually if needed
# Column with cumulative number of positive cases should be called positive, daily new cases newcases
names(covid_data)[names(covid_data) == "Pocet.potvrdenych"] <- "positive"
names(covid_data)[names(covid_data) == "Dennych.prirastkov"] <- "newcases"

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

# Compute k_t_constant + dow
foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
  day=paste("day_",d,sep="")
  if (d == "Sunday") {
    last42$k_t_constant_dow[last42[, day] == 1] <- last42$k_t_constant[last42[, day] == 1]
  } else {
    last42$k_t_constant_dow[last42[, day] == 1] <- last42$k_t_constant[last42[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
  }
}

# Compute k_t_constant + dow
foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
  day=paste("day_",d,sep="")
  if (d == "Sunday") {
    test$k_t_constant_dow[test[, day] == 1] <- test$k_t_constant[test[, day] == 1]
  } else {
    test$k_t_constant_dow[test[, day] == 1] <- test$k_t_constant[test[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
  }
}

# Plot
p <- ggplot() +
  # last 42 days
  geom_point(data=last42, aes(x=date, y=k_t_star)) +
  # predicted 14 days of test window
  geom_line(data=test, aes(x=date, y=k_t_constant))

last42$k<- seq(14, length.out=nrow(last42), by=-1)
test$k<- seq(14, length.out=nrow(test), by=-1)

median_k_t<-median(as.vector(training$k_t_star_pred[1:7]))

# Generate grid of parameters for joint distribution
seq_phi<-seq(0.90, 1.20, by=0.01)
seq_omega<-seq(1, 60, by=1)
seq_eta<-seq(0, 1, by=0.01)
complete_dist<-expand.grid(seq_eta, seq_omega, seq_phi)

dist<-cbind(0, 0, 0, 0)
for (row in 1:nrow(complete_dist)) {
  leta<-complete_dist[row, "Var1"]
  lomega<-complete_dist[row, "Var2"]
  lphi<-complete_dist[row, "Var3"]
  dist<-rbind(dist, joint_dist(leta, lomega, lphi))
}

# Normalize the distance
dist<-cbind(dist, (dist[,4]-min(dist[,4]))/(max(dist[,4])-min(dist[,4])))
dist<-dist[order(-dist[,5]),]
# Forecast on test window
test$k_t_forecast<-rev(k_t_forecast(dist[1,1],dist[1,2],dist[1,3],test))

p <- ggplot() +
# Last 42 days
geom_point(data=last42, aes(x=date, y=k_t_star)) +
geom_line(data=last42, aes(x=date, y=k_t_star)) +
# Predicted 14 days of test window
geom_line(data=test, aes(x=date, y=k_t_forecast))

####
# True forecast
# Subset new training data
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
# Plot
p <- ggplot() +
# Last 27 days
geom_point(data=new_training, aes(x=date, y=k_t_star)) +
geom_line(data=new_training, aes(x=date, y=k_t_star_pred)) +
# Predicted 14 days of test window
geom_line(data=forecast, aes(x=date, y=k_t_star_pred))

# Number of new daily cases
new_training$newcases=new_training$positive-lead(new_training$positive)

# Average number of daily cases reported over the last week of the training window
y_ct_avg_forecast<-sum(new_training$newcases[1:7])/7

# Fit k_t_constant trajectory for the forecasting data
k_t_constant14<-head(subset(new_training, select=c("date", "positive", "n")), 14)

k_t_constant14$k_t_constant<-logit(y_ct_avg_forecast*(((ar*pop-lead(k_t_constant14$positive))/(ar*pop))*lead(k_t_constant14$positive))^-1)
k_t_constant14[14, "k_t_constant"]<-logit(y_ct_avg_forecast*(((ar*pop-lead(k_t_constant14[14, "positive"]))/(ar*pop))*new_training[15, "positive"])^-1)
k_t_cons_pred<-lm(k_t_constant ~ n, data=k_t_constant14)
forecast$k_t_constant=predict(k_t_cons_pred, newdata = forecast)


# Compute k_constant + dow
foreach (d = c("Monday","Tuesday","Wednesday","Thursday","Friday","Saturday","Sunday"), i = 3:9) %do% {
    day=paste("day_",d,sep="")
    if (d == 'Sunday') {
    forecast$k_t_constant_dow[forecast[, day] == 1] <- forecast$k_t_constant[forecast[, day] == 1]
    } else {
    forecast$k_t_constant_dow[forecast[, day] == 1] <- forecast$k_t_constant[forecast[, day] == 1]+summary(weighted_model)$coefficients[i, 1]
    }
}

median_k_t<-median(as.vector(new_training$k_t_star_pred[1:7]))
forecast$k<- seq(K, length.out=nrow(forecast), by=-1)

# Draw from joint distribution
param<-cbind(dist[sample(nrow(dist), 1, prob=dist[, 4]), 1:3])

# Forecast cases for three scenarios
# Note that by default the forecasting function uses a vector of randomly drawn parameters
for (s_phi in c(best, mid, worst)) {

if (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27) {
    forecast$y_s_forecast<-rbinom(K,1,1/28)
    } else if (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14) {
    forecast$y_s_forecast<-sample(new_training$newcases, K, replace = TRUE)
  } else {
    
forecast$k_t_forecast<-rev(k_t_forecast(param[1,1],param[2,1],s_phi,forecast))
forecast$inv_k_t_forecast<-inv.logit(forecast$k_t_forecast)

d_s_forecast=runif(1,0.4,0.7)*pop
d_s_T=d_s_forecast-new_training[1,2]

forecast['d_c_forecast'] <- NA
forecast['d_c_dot_forecast'] <- NA
forecast['d_s_forecast'] <- NA

for (row in K:1) {
  if (row == K) {
    forecast[row,'d_c_forecast']<-forecast[row, 'inv_k_t_forecast']*(d_s_T/d_s_forecast)*new_training[1,2]
    forecast[row,'d_c_dot_forecast']<-new_training[1,2]+forecast[row,'d_c_forecast']
    forecast[row,'d_s_forecast']<-d_s_T-forecast[row,'d_c_forecast']
  } else {
    forecast[row,'d_c_forecast']<-forecast[row, 'inv_k_t_forecast']*(forecast[row+1,'d_s_forecast']/d_s_forecast)*
      forecast[row+1,'d_c_dot_forecast']
    forecast[row,'d_c_dot_forecast']<-forecast[row+1,'d_c_dot_forecast']+forecast[row,'d_c_forecast']
    forecast[row,'d_s_forecast']<-forecast[row+1,'d_s_forecast']-forecast[row,'d_c_forecast']
  }
}  

# Round number of cases
forecast$d_c_forecast<-round(forecast$d_c_forecast)
forecast['y_s_forecast'] <- NA
nb<-ml.nb1(formula = d_c_forecast ~ 1, data=forecast)
for (row in 1:K) {
  forecast[row, "y_s_forecast"]<-qnbinom(0.50,mu=forecast[row,"d_c_forecast"],size=forecast[row,"d_c_forecast"]/nb[2, "Estimate"])
}

# Smoothing of the cases line
smoothing<-loess(formula = y_s_forecast ~ n, data=forecast, span=0.7)
forecast$smoothed_cases<-predict(smoothing)

if (s_phi==worst) { scenario="Worst case"} else if (s_phi==mid) {scenario="Mid case"} else if (s_phi==best) { scenario ="Best case"}

# Plot
p <- ggplot() +
  # Observed data
  geom_line(data=new_training, aes(x=date, y=newcases), colour="gray78")+
  geom_point(data=new_training, aes(x=date, y=newcases), shape=21, colour="black", fill="#cc0066", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(new_training$date[1])), linetype="dashed")+
  # Forecast
  geom_point(data=forecast, aes(x=date, y=y_s_forecast), shape=21, colour="black", fill="#b3c6ff", size=3, stroke=0.2) +
  geom_line(data=forecast, aes(x=date, y=y_s_forecast), colour="gray78")+
  geom_ribbon(data=forecast, aes(ymin=smoothed_cases-50, ymax=smoothed_cases+50, x=date), colour="gray78", fill="#b3c6ff",alpha=0.4)+
  scale_x_date(date_breaks = "weeks")+xlab("Date")+ylab("Daily new cases")+ggtitle(scenario)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), plot.title = element_text(hjust = 0.5))  
 
ggsave(paste(scenario,".pdf",sep=""),
  plot = p, device = "pdf",
  path = output_folder,
  dpi = 300
)

# Hospitalizations
forecast_hosp<-subset(forecast, select=c("date", "y_s_forecast"))
names(forecast_hosp)[names(forecast_hosp) == "y_s_forecast"] <- "newcases"
forecast_hosp<-rbind(forecast_hosp, subset(covid_data, select=c("date", "newcases")))

forecast_hosp$newcases_shift<-shift(forecast_hosp$newcases, n=6, fill=NA, type="lead")
forecast_hosp<-head(forecast_hosp, nrow(forecast_hosp)-6)

hosp<-hospitalizations(hosp_share*forecast_hosp$newcases_shift, forecast_hosp$date, los, 30)
r_up=nrow(hosp)
r_low=nrow(hosp)-50
plot(hosp[r_up:r_low], quantiles = c(0.01, 0.05, 0.5, 0.95, 0.99), xlab("Hospitalizations"))+
  theme_bw()+ggtitle(scenario)+theme(plot.title = element_text(hjust = 0.5))+
  geom_vline(xintercept=(xintercept=as.numeric(new_training$date[1])), linetype="dashed")

ggsave(paste(scenario," hospitalizations.pdf",sep=""),
       plot = last_plot(), device = "pdf",
       path = output_folder,
       dpi = 300
)

# Write csv files with exported data
hosp_median<-unname(apply(hosp[-2], 1, FUN=quantile, probs=c(0.5), na.rm=TRUE))
export<-data.frame(forecast_hosp[1:length(hosp_median),1], forecast_hosp[1:length(hosp_median),2], rev(hosp_median))
colnames(export) <- c("date", "newcases", "hospitalizations")
write.csv(export, file = paste(output_folder,scenario,".csv",sep=""), )
}
}