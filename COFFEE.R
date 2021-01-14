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
library("data.table")
library("fitdistrplus")

# Set system locale to EN/US due to english week days
# Windows: Sys.setlocale(category = "LC_ALL", locale = "English_United States.1252")
# *NIX: Sys.setlocale("LC_TIME", "en_US")

# define some constants/variables
data="https://raw.githubusercontent.com/Institut-Zdravotnych-Analyz/covid19-data/main/OpenData_Slovakia_Covid_DailyStats.csv"
# Population of the forecasted area
pop=5458000
# Forecast window size in days
K=48
# Nominal attack rate of covid-19
ar=0.55
# Share of people hospitalized, based on admissions data
hosp_share=0.061
# Share of hospitalized needing ICU
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
  return(forecast)
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
  inv_k_t_forecast<-inv.logit(int)
  
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
los_h <- distcrete::distcrete("weibull", shape = 1.3, scale = 10.339, w = 0, interval = 1)
los_v <- distcrete::distcrete("weibull", shape = 1.32, scale = 10.984, w = 0, interval = 1)

####

hospital_data<-read.csv(url(hosp_data), header = TRUE, sep=";")
hospital_data$date <- as.Date(hospital_data$Datum)

vent_data <- hospital_data %>% group_by(date) %>% summarise_(ventilated="sum(Plucna_vent_lozka)")
vent_data<-vent_data[seq(dim(vent_data)[1],1),]
vent_data<-tail(vent_data, -1) 

hospital_data <- hospital_data %>% group_by(date) %>% summarise_(hospitalized="sum(hospitalizovany)")
hospital_data<-hospital_data[seq(dim(hospital_data)[1],1),]
hospital_data<-tail(hospital_data, -1)

covid_data<-read.csv(url(data), header = TRUE, sep=";")
covid_data<-covid_data[seq(dim(covid_data)[1],1),]
covid_data$date <- as.Date(covid_data$Datum)
# Rename columns manually if needed
# Column with cumulative number of positive cases should be called positive, daily new cases newcases
names(covid_data)[names(covid_data) == "Pocet.potvrdenych"] <- "positive"
names(covid_data)[names(covid_data) == "Dennych.prirastkov"] <- "newcases"
covid_data$AgPosit[is.na(covid_data$AgPosit)]<-0
covid_data$newcases<-covid_data$newcases+covid_data$AgPosit
covid_data<-covid_data%>%mutate(positive=rev(cumsum(rev(newcases))))

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

####
# Outlier detection
# A linear trend with DOW effects is first estimated over the last 42 days of the data
# Observations falling outside of 3*mean of the Cook's distance are labeled as outliers and adjusted 
# to the mean number of cases at days t-7, t+7, t-14. If the any of the indexes is non-existent, the mean is calculated from the available ones
mod <- lm(newcases ~ n + day_Monday + day_Tuesday + day_Wednesday + day_Thursday + day_Friday + day_Saturday, data=last42)
last42$cookd <- cooks.distance(mod)

last42$outlier<-0
last42$index<-seq(1,nrow(last42))
last42$outlier[last42$cookd>3*mean(last42$cookd, na.rm=T)]=1

p_outliers<-
  last42 %>%
  mutate(color = if_else(last42$outlier==1, "Outlier", "Normal")) %>%
  ggplot()+geom_point(aes(x=date, y=cookd, fill=color), shape=21, colour="black", size=3, stroke=0.2)+
  geom_text_repel(aes(label = ifelse(outlier==1,format(date, format = "%b %d"), ""), x=date, y=cookd))+
  scale_fill_manual(values = c("Outlier" = "hotpink3", "Normal" = "gray"))+
  geom_hline(yintercept=3*mean(last42$cookd, na.rm=T), linetype="dashed")+
  xlab("Date")+ylab("Cook's distance")+theme_bw()+theme(legend.position="none")

for (i in which(last42$outlier==1)) {
  last42[i, "adjustedcases"]<-round(mean(c(
    if (length(last42[last42$index==i+7 &  last42$outlier==0, "newcases"])>0) {
      last42[last42$index==i+7 &  last42$outlier==0, "newcases"]},
    if (length(last42[last42$index==i-7 &  last42$outlier==0, "newcases"])>0) {
      last42[last42$index==i-7 &  last42$outlier==0, "newcases"]},
    if (length(last42[last42$index==i+14 &  last42$outlier==0, "newcases"])>0) {
      last42[last42$index==i+14 &  last42$outlier==0, "newcases"]}
  )))
  
}

for (i in which(last42$outlier==1)) {
  last42[i, "positive"]<-last42[i, "positive"]-(last42[i, "newcases"]-last42[i, "adjustedcases"])
  last42[1:(i-1), "positive"]<-last42[1:(i-1), "positive"]-(last42[i, "newcases"]-last42[i, "adjustedcases"])
}
last42[last42$outlier==1, "newcases"]<-last42[last42$outlier==1, "adjustedcases"]

#####
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
p_k_t_star <- ggplot() +
  # Last 42 days
  geom_point(data=training, aes(x=date, y=k_t_star), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_line(data=training, aes(x=date, y=k_t_star_pred))+
  geom_vline(xintercept=(xintercept=as.numeric(training$date[1])), linetype="dashed")+
  # Predicted 14 days of test window
  geom_point(data=test, aes(x=date, y=k_t_star), shape=24, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_line(data=test, aes(x=date, y=k_t_star_pred))+ylab(expression(hat(kappa)[t]^{"*"}))+xlab("Date")+theme_bw()

# Average number of daily cases reported over the last week of the training window
y_ct_avg<-sum(last42$newcases[15:21])/7

last42$k_t_constant=logit(y_ct_avg*(((ar*pop-lead(last42$positive))/(ar*pop))*lead(last42$positive))^-1)
test$k_t_constant=logit(y_ct_avg*(((ar*pop-lead(test$positive))/(ar*pop))*lead(test$positive))^-1)
test[14, 'k_t_constant']=logit(y_ct_avg*(((ar*pop-last42[15, 'positive'])/(ar*pop))*last42[15, 'positive'])^-1)

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

# Plot k_t_constant
p_k_t_constant <- ggplot() +
  # Last 42 days
  geom_point(data=training, aes(x=date, y=k_t_star), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_vline(xintercept=(xintercept=as.numeric(training$date[1])), linetype="dashed")+
  # Predicted 14 days of test window
  geom_point(data=test, aes(x=date, y=k_t_star), shape=24, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_line(data=test, aes(x=date, y=k_t_constant))+ylab(expression(hat(kappa)[t]^{"*"}))+xlab("Date")+theme_bw()

last42$k<- seq(14, length.out=nrow(last42), by=-1)
test$k<- seq(14, length.out=nrow(test), by=-1)

median_k_t<-median(as.vector(training$k_t_star[1:7]))

# Generate a grid of parameters for the joint distribution
seq_phi<-seq(0.90, 1.10, by=0.2/14)
seq_omega<-seq(3, 62, by=3)
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

# Plot the distribution
distr_plot<-as.data.frame(distr)
p_distr<-ggplot(distr_plot, aes(V2, V3)) + geom_tile(aes(fill = V5))+facet_wrap(~ V1, ncol=5)+
  scale_fill_gradient("Prob", low="#D2D2D2", high="black",breaks=c(min(distr_plot$V5),max(distr_plot$V5)), labels=c("Low","High"))+
  xlab(expression(omega))+ylab(expression(phi))+theme_bw()

# Plot trajcetories of the forecast distribution
forecast_dist<-mapply(k_t_forecast,distr[,1],distr[,2],distr[,3])
forecast_dist<-as.data.frame(forecast_dist)
forecast_dist$date<-test$date
forecast_dist<-melt(forecast_dist, "date")
forecast_dist$prob<-unlist(lapply(distr[,5], rep, 14))
forecast_dist$variable <- factor(forecast_dist$variable, levels=rev(levels(forecast_dist$variable)))
p_distr_traject<-ggplot()+geom_line(data=forecast_dist, aes(x=date, y=value, group=variable, color=prob),size=1, alpha=0.3)+
                  geom_point(data=training, aes(x=date, y=k_t_star), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2)+
                  geom_point(data=test, aes(x=date, y=k_t_star), shape=24, colour="black", fill="hotpink3", size=3, stroke=0.2)+
                  geom_vline(xintercept=(xintercept=as.numeric(training$date[1])), linetype="dashed")+
                  scale_color_gradient("Prob", low="#D2D2D2", high="black",
                  breaks=c(min(forecast_dist$prob),max(forecast_dist$prob)), labels=c("Low","High"))+
                  ylab(expression(hat(kappa)[t]^{"*"}))+xlab("Date")+theme_bw()

# Plot the best fit of k_t_forecast
p_k_t_forecast_fit <- ggplot() +
  # Training
  geom_point(data=training, aes(x=date, y=k_t_star), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_vline(xintercept=(xintercept=as.numeric(training$date[1])), linetype="dashed")+
  # Predicted 14 days of test window
  geom_point(data=test, aes(x=date, y=k_t_star), shape=24, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_line(data=test, aes(x=date, y=k_t_forecast))+ylab(expression(hat(kappa)[t]^{"*"}))+xlab("Date")+theme_bw()

####
# True forecast
# Subsetnew training data
new_training <-subset(last42[1:27,], select=c("date", "positive", "newcases", "k_t", "k_t_star", "n", "day_Friday", "day_Monday", "day_Saturday",
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
p_k_t_forecast <- ggplot() +
  geom_point(data=new_training, aes(x=date, y=k_t_star), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_vline(xintercept=(xintercept=as.numeric(new_training$date[1])), linetype="dashed")+
  geom_point(data=forecast, aes(x=date, y=k_t_star_pred), shape=24, colour="black", fill="hotpink3", size=3, stroke=0.2)+
  geom_line(data=forecast, aes(x=date, y=k_t_star_pred))+geom_line(data=forecast, aes(x=date, y=k_t_constant_dow), linetype="dashed")+
  ylab(expression(hat(kappa)[t]^{"*"}))+xlab("Date")+theme_bw()

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

# Plot
colors <- c("Median" = "black", "80% prediction interval" = "deeppink", "50% prediction interval" = "hotpink3")

p_cases <- ggplot() +
  # Real data
  geom_line(data=covid_data[1:K,], aes(x=date, y=newcases), colour="gray78")+
  geom_point(data=covid_data[1:K,], aes(x=date, y=newcases), shape=21, colour="black", fill="hotpink3", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(new_training$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks", date_labels = "%b-%d")+xlab("Date")+ylab("Daily new cases")+scale_y_continuous(labels = scales::comma)
  
  plot_intervals <- function(point = FALSE){
    list(
      if (! (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27 | sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14)) 
          geom_ribbon(data=forecast, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
          geom_ribbon(data=forecast, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
    )
  }
  
  p_cases<-p_cases+plot_intervals()+scale_color_manual(values = colors)+scale_fill_manual(values = colors)+
    geom_line(data=forecast, aes(x=date, y=X0.5, colour="Median"), size=1)+
    theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.title=element_blank(), legend.position="bottom")
    
ggsave("Cases.pdf",
       plot = last_plot(), device = "pdf",
       path = output_folder,
       dpi = 300
)

# Create sheet
cases_summary<-rbind.fill(forecast[, names(forecast) %in% c("date", colnames_int)], last42[, names(last42) %in% c("date", "newcases")])

# Forecast hospitalizations
# Initialize the forecast with the current number of hospitalized
current_beds=hospital_data$hospitalized[date=which.max(hospital_data$date)]

forecast_hosp<-forecast[, names(forecast) %in% c("date", colnames_int)]

forecast_hosp[,2:ncol(forecast_hosp)]<-forecast_hosp[,2:ncol(forecast_hosp)]*hosp_share
forecast_hosp[K,2:ncol(forecast_hosp)]<-current_beds

hosp_list<-lapply(forecast_hosp[,2:ncol(forecast_hosp)], hospitalizations, forecast_hosp[,1], los_h, 30)

if ("X0.5" %in% colnames(forecast_hosp)) {
  forecast_hosp <- forecast_hosp[, ! names(forecast_hosp) %in% colnames_int, drop = F]
}
forecast_hosp<-cbind(forecast_hosp, sapply(names(hosp_list), function(x) apply(hosp_list[[x]], 1, stats::quantile, probs=as.numeric(substring(x,2)))))
forecast_hosp[,2:ncol(forecast_hosp)]<-forecast_hosp[dim(forecast_hosp[,2:ncol(forecast_hosp)])[1]:1,2:ncol(forecast_hosp)]
row.names(forecast_hosp) <- NULL

# Smoothing of the prediction
smoothing<-loess(formula = X0.5 ~ as.numeric(date), data=forecast_hosp, span=0.32)
forecast_hosp$X0.5<-predict(smoothing)
if (! (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27 | sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14)) {
  smoothing<-loess(formula = X0.1 ~ as.numeric(date), data=forecast_hosp, span=0.32)
  forecast_hosp$X0.1<-predict(smoothing)
  smoothing<-loess(formula = X0.25 ~ as.numeric(date), data=forecast_hosp, span=0.32)
  forecast_hosp$X0.25<-predict(smoothing)
  smoothing<-loess(formula = X0.75 ~ as.numeric(date), data=forecast_hosp, span=0.32)
  forecast_hosp$X0.75<-predict(smoothing)
  smoothing<-loess(formula = X0.9 ~ as.numeric(date), data=forecast_hosp, span=0.32)
  forecast_hosp$X0.9<-predict(smoothing)
}

# Create sheet
hosp_summary<-rbind.fill(forecast_hosp, hospital_data[1:42, names(hospital_data) %in% c("date", "hospitalized")])

# Plot
colors_h <- c("Median" = "black", "80% prediction interval" = "darkorchid1", "50% prediction interval" = "darkorchid4")

p_hosp <- ggplot() +
  geom_line(data=hosp_summary, aes(x=date, y=hospitalized), colour="gray78")+
  geom_point(data=hosp_summary, aes(x=date, y=hospitalized), shape=21, colour="black", fill="darkorchid4", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(hospital_data$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks", date_labels = "%b-%d")+xlab("Date")+ylab("Hospitalized")+scale_y_continuous(labels = scales::comma)

plot_intervals_h <- function(point = FALSE){
  list(
    if ("X0.9" %in% colnames(hosp_summary)) 
      geom_ribbon(data=hosp_summary, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
    geom_ribbon(data=hosp_summary, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
  )
}

p_hosp<-p_hosp+plot_intervals_h()+scale_color_manual(values = colors_h)+scale_fill_manual(values = colors_h)+
  geom_line(data=hosp_summary, aes(x=date, y=X0.5, colour="Median"), size=1)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.position="bottom", 
  legend.title=element_blank(), plot.title = element_text(hjust = 0.5))

ggsave("Hospitalized.pdf",
       plot = last_plot(), device = "pdf",
       path = output_folder,
       dpi = 300
)

# Forecast ICU ventilated
current_vent=vent_data$ventilated[date=which.max(vent_data$date)]

forecast_vent<-forecast[, names(forecast) %in% c("date", colnames_int)]

forecast_vent[,2:ncol(forecast_vent)]<-forecast_vent[,2:ncol(forecast_vent)]*hosp_share*vent_share
forecast_vent[K,2:ncol(forecast_vent)]<-current_vent

vent_list<-lapply(forecast_vent[,2:ncol(forecast_vent)], hospitalizations, forecast_vent[,1], los_v, 30)

if ("X0.5" %in% colnames(forecast_vent)) {
  forecast_vent <- forecast_vent[, ! names(forecast_vent) %in% colnames_int, drop = F]
}
forecast_vent<-cbind(forecast_vent, sapply(names(vent_list), function(x) apply(vent_list[[x]], 1, stats::quantile, probs=as.numeric(substring(x,2)))))
forecast_vent[,2:ncol(forecast_vent)]<-forecast_vent[dim(forecast_vent[,2:ncol(forecast_vent)])[1]:1,2:ncol(forecast_vent)]
row.names(forecast_vent) <- NULL

# Smoothing of the prediction
smoothing<-loess(formula = X0.5 ~ as.numeric(date), data=forecast_vent, span=0.32)
forecast_vent$X0.5<-predict(smoothing)
if (! (sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)==27 | sum(new_training[1:27, "newcases"]==0, na.rm=TRUE)>=14)) {
  smoothing<-loess(formula = X0.1 ~ as.numeric(date), data=forecast_vent, span=0.32)
  forecast_vent$X0.1<-predict(smoothing)
  smoothing<-loess(formula = X0.25 ~ as.numeric(date), data=forecast_vent, span=0.32)
  forecast_vent$X0.25<-predict(smoothing)
  smoothing<-loess(formula = X0.75 ~ as.numeric(date), data=forecast_vent, span=0.32)
  forecast_vent$X0.75<-predict(smoothing)
  smoothing<-loess(formula = X0.9 ~ as.numeric(date), data=forecast_vent, span=0.32)
  forecast_vent$X0.9<-predict(smoothing)
}

# Create sheet
vent_summary<-rbind.fill(forecast_vent, vent_data[1:42, names(vent_data) %in% c("date", "ventilated")])

# Plot
colors_c <- c("Median" = "black", "80% prediction interval" = "deeppink", "50% prediction interval" = "hotpink3")

p_vent <- ggplot() +
  geom_line(data=vent_summary, aes(x=date, y=ventilated), colour="gray78")+
  geom_point(data=vent_summary, aes(x=date, y=ventilated), shape=21, colour="black", fill="steelblue4", size=3, stroke=0.2) +
  geom_vline(xintercept=(xintercept=as.numeric(vent_data$date[1])), linetype="dashed")+
  scale_x_date(date_breaks = "weeks", date_labels = "%b-%d")+xlab("Date")+ylab("Ventilated")+scale_y_continuous(labels = scales::comma)

plot_intervals_v <- function(point = FALSE){
  list(
    if ("X0.9" %in% colnames(vent_summary)) 
      geom_ribbon(data=vent_summary, aes(x=date, ymin=X0.1, ymax=X0.9, fill="80% prediction interval"), alpha=0.5),
    geom_ribbon(data=vent_summary, aes(x=date, ymin=X0.25, ymax=X0.75, fill="50% prediction interval"), alpha=0.5)
  )
}

p_vent<-p_vent+plot_intervals_v()+scale_color_manual(values = colors_v)+scale_fill_manual(values = colors_v)+
  geom_line(data=vent_summary, aes(x=date, y=X0.5, colour="Median"), size=1)+
  theme_bw()+theme(axis.text.x = element_text(angle = 45, vjust = 0.5, hjust=0.5), legend.position="bottom", 
  legend.title=element_blank(), plot.title = element_text(hjust = 0.5))

ggsave("ICU ventilated.pdf",
       plot = last_plot(), device = "pdf",
       path = output_folder,
       dpi = 300
)

write.csv(hosp_summary, file = paste(output_folder,"Hospitalizations.csv",sep=""), )
write.csv(vent_summary, file = paste(output_folder,"ICU ventilated.csv",sep=""), )
write.csv(cases_summary, file = paste(output_folder,"Cases.csv",sep=""), )