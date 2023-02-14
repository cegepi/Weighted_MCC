/********************************************************************************************************************************************************
MACRO NAME: MCCWEIGHT 
AUTHORS: Charles E. Gaber, Jessie K. Edwards, Jennifer L. Lund, Anne F. Peery, David B. Richardson, Alan C. Kinlaw 

NOTES:
This macro is largely a modification of the macro created by Dong et. al and presented in their 2015 publication in AJE:

Dong H, Robison LL, Leisenring WM, Martin LJ, Armstrong GT, Yasui Y. 
Estimating the burden of recurrent events in the presence of competing risks: The method of mean cumulative count. 
American Journal of Epidemiology. 2015;181(7):532-540. doi:10.1093/aje/kwu289

While this MCCWEIGHT macro was written from scratch, it borrows coding techniques heavily (sometimes verbatim) from 
existing code created and shared by Dong et al. 

Two main additions present in this MCCWEIGHT macro include: 
1) The incorporation of a treatment group variable
2) the incorporation of weights into the non-parametric MCC estimator.

This MCCWEIGHT macro is designed to be used *after* the analyst has performed bootstrap re-sampling 
and stacked all of the resamples into one dataset. This must include a variable called REPLICATE that 
indicates the bootstrap resample number and the original (pre-bootstrapping) sample should be in this 
dataset with a REPLICATE value of 0 – we like to put it at the top of the dataset before REPLICATE 1. 
Remember, weights should be constructed in each bootstrap resample separately. Also, a given ID can 
have multiple rows – the rows are each time an event of interest (Y=1), competing event (Y=2), or 
censoring event (Y=0) occurs. Additionally, the same person (and all their rows) may be in the same 
replicate more than once given that bootstrap resampling uses sampling with replacement. 


INPUT MACRO PARAMETER VARIABLES:

	DATANAME = name of the analytic dataset
	BOOTNUM = The number of bootstrap resamples used in the input dataset (numeric constant)
	ID = unique subject ID variable
	STATUS = variable that takes on the values:
				0 = censored
				1 = event of interest
				2 = competing event
	TIME = variable that is the time since cohort entry corresponding to the STATUS variable
	TRT = binary treatment variable that takes on the values:
				0 = reference treatment
				1 = index treatment
	WT = weight variable (example: could be a stabilized inverse-probability of treatment weight)
	ENDFOLLOWUP = the maximum follow-up time on the x-axis, in the units the data were observed in (e.g. 365 for 365 days of follow-up)

********************************************************************************************************************************************************/

%macro MCCWEIGHTBOOT (dataname=, bootnum=, id=, status=, time=, trt=, wt=, endfollowup=);

Data originalpats;
	set &dataname.;
	where replicate=0; Run;

Proc sort data=originalpats nodupkey out=originalpats;
	by &id.; Run;

Proc sql;
	create table sumwtpat as
	select &trt., sum (&wt.) as wtpat
	from originalpats
	where replicate=0
	group by &trt.; quit;

Proc sql;
	select wtpat
		into :ntrt1
		from sumwtpat
		where &trt.=1;
	select wtpat
		into :ntrt2
		from sumwtpat
		where &trt.=0; quit;
%put &ntrt1.;
%put &ntrt2.;

Data mcctemp1;
	set &dataname.;
	where replicate=0;
	if &status.=0 then censor_ind=1;
		else censor_ind=0;
	if &status.=1 then event_ind=1;
		else event_ind=0;
	if &status.=2 then comp_ind=1;
		else comp_ind=0;
	censored_weight=censor_ind*&wt.;
	event_weight=event_ind*&wt.;
	comp_weight=comp_ind*&wt.; Run;

Proc sql;
	create table mcctemp2 as
	select &trt., &time., sum(censored_weight) as tot_censor, sum(event_weight) as tot_event, sum(comp_weight) as tot_comp
	from mcctemp1
	group by &trt., &time.; quit;

Data mcctemp2;
	set mcctemp2;
	by &trt.;
	If first.&trt. then do;
		censor_runningtot= tot_censor;
		event_runningtot= tot_event;
		comp_runningtot= tot_comp;
		output;
	end;
	else do;
		censor_runningtot + tot_censor;
		event_runningtot + tot_event;
		comp_runningtot + tot_comp;
		output;
	end; Run;

Data mcctemp2;
	set mcctemp2;
	by &trt.;
	if &trt.=1 then do;
		atrisk=&ntrt1. - censor_runningtot - comp_runningtot;
		atrisk_previous=ifn(first.&trt., &ntrt1., lag(atrisk));
		survt= 1 - (tot_comp/atrisk_previous);
	end;
	if &trt.=0 then do;
		atrisk=&ntrt2. - censor_runningtot - comp_runningtot;
		atrisk_previous=ifn(first.&trt., &ntrt2., lag(atrisk));
		survt= 1 - (tot_comp/atrisk_previous);
	end; Run;

proc expand data=mcctemp2 out=mcctemp3;
	by &trt.;
	id &time.;
	convert survt=km/transformout=(cuprod); run;

Data mcctemp3;
	set mcctemp3;
	by &trt.;
	km_previous=ifn(first.&trt., 1, lag(km));
	count= (tot_event/atrisk_previous)*km_previous; Run;

Data mccfinal;
set mcctemp3;
   by &trt.;
   if first.&trt. then mcc=count;
   mcc + count; run;

Proc datasets library=work;
	delete mcctemp1 mcctemp2 mcctemp3; Run;

Data mccfinal;
	set mccfinal; output;
	by &trt.;
	if first.&trt. then do;
		&time.=0; 
		mcc=0;
		output;
		end; Run;
Proc sort data=mccfinal;
	by &trt. &time.; Run;
Data uniquetimes;
	do &time.= 0 to &endfollowup.;
	replicate=0;
		output;
	end; Run;
Data zero;
	set mccfinal;
	where &trt.=0;
	treatment="zero"; Run;
Data one;
  	set mccfinal;
	where &trt.=1;
	treatment="one"; Run;
Proc sql;
  	create table mcc_point as
	select a.replicate, a.&time., b.mcc as mcc_zero, c.mcc as mcc_one
	from uniquetimes as a
	left join zero as b
	on a.&time.=b.&time.
	left join one as c
	on a.&time.=c.&time.; quit;

*This code makes missing values of MCC (to be expected, an event likely doesn't occur at every unique day of follow-up)
retain the most recent value of the MCC. This will generate the plateaus in the step function;
Data mcc_point;
	set mcc_point;
	retain _mcc0 _mcc1;
	if not missing(mcc_zero) then _mcc0=mcc_zero;
		else mcc_zero=_mcc0;
	drop _mcc0;
	if mcc_zero=. then mcc_zero=lag(mcc_zero);

	if not missing(mcc_one) then _mcc1=mcc_one;
		else mcc_one=_mcc1;
	drop _mcc1;
	if mcc_one=. then mcc_one=lag(mcc_one); Run;
Data mcc_point;
	set mcc_point;
	MCCD=mcc_one-mcc_zero;
	MCCR=mcc_one/mcc_zero; Run;
Data mcc_point;
	set mcc_point;
	if MCCR=. then MCCR=1.00000; Run;

******PERFORMING CALCULATIONS BY BOOTSTRAP RESAMPLE TO GET STANDARD ERROR******;

Data originalpats;
	set &dataname.;
	where replicate^=0; Run;

Proc sql;
		create table first as
		select replicate, &id., &time., &trt., sum (&wt.) as wtpat_first
		from originalpats
		group by replicate, &id., &time., &trt.; quit;

Proc sort data=first nodupkey out=first;
	by replicate &id.; Run;

Proc sql;
	create table sumwtpat as
	select replicate, &trt., sum (wtpat_first) as wtpat
	from first
	group by replicate, &trt.; quit;

Proc sql;
	select wtpat
		into :ntrtone1 - :ntrtone&bootnum.
		from sumwtpat
		where &trt.=1;
	select wtpat
		into :ntrttwo1 - :ntrttwo&bootnum.
		from sumwtpat
		where &trt.=0; quit;

Data mcctemp1;
	set &dataname.;
	where replicate^=0;
	if &status.=0 then censor_ind=1;
		else censor_ind=0;
	if &status.=1 then event_ind=1;
		else event_ind=0;
	if &status.=2 then comp_ind=1;
		else comp_ind=0;
	censored_weight=censor_ind*&wt.;
	event_weight=event_ind*&wt.;
	comp_weight=comp_ind*&wt.; Run;

Proc sql;
	create table mcctemp2 as
	select replicate, &trt., &time., sum(censored_weight) as tot_censor, sum(event_weight) as tot_event, sum(comp_weight) as tot_comp
	from mcctemp1
	group by replicate, &trt., &time.; quit;

Data mcctemp2;
	set mcctemp2;
	by replicate &trt.;
	If first.&trt. then do;
		censor_runningtot= tot_censor;
		event_runningtot= tot_event;
		comp_runningtot= tot_comp;
		output;
	end;
	else do;
		censor_runningtot + tot_censor;
		event_runningtot + tot_event;
		comp_runningtot + tot_comp;
		output;
	end; Run;

Data mcctemp2;
	set mcctemp2;
	by replicate &trt.;
	if &trt.=1 then do;
		atrisk=symget('ntrtone'||LEFT(replicate)) - censor_runningtot - comp_runningtot;
		atrisk_previous=ifn(first.&trt., symget('ntrtone'||LEFT(replicate)), lag(atrisk));
		survt= 1 - (tot_comp/atrisk_previous);
	end;
	if &trt.=0 then do;
		atrisk=symget('ntrttwo'||LEFT(replicate)) - censor_runningtot - comp_runningtot;
		atrisk_previous=ifn(first.&trt., symget('ntrttwo'||LEFT(replicate)), lag(atrisk));
		survt= 1 - (tot_comp/atrisk_previous);
	end; Run;

proc expand data=mcctemp2 out=mcctemp3;
	by replicate &trt.;
	id &time.;
	convert survt=km/transformout=(cuprod); run;

Data mcctemp3;
	set mcctemp3;
	by replicate &trt.;
	km_previous=ifn(first.&trt., 1, lag(km));
	count= (tot_event/atrisk_previous)*km_previous; Run;

Data mccfinal;
set mcctemp3;
   by replicate &trt.;
   if first.&trt. then mcc=count;
   mcc + count; run;

*This creates the zero value of mcc at the origin (time 0)*;
data mccfinal;
	set mccfinal;
	by replicate &trt.;
	output;
if first.&trt. then do;
   &time.=0;
   mcc=0;
   output;
  end; Run;

Proc sort data=mccfinal;
	by replicate &trt. &time.; Run;

Data uniquetimes;
	do &time.= 0 to &endfollowup.;
		output;
	end; Run;

*Expand it for each replicate*;
data uniquetimes;
   do replicate = 1 to &bootnum.;
      do j = 1 to n;
         set uniquetimes nobs=n point=j;
         output;
         end;
      end;
   stop; run;

Data zero;
	set mccfinal;
	where &trt.=0;
	treatment="zero"; Run;

Data one;
  	set mccfinal;
	where &trt.=1;
	treatment="one"; Run;

Proc sql;
  	create table mcc_boot as
	select a.replicate, a.&time., b.mcc as mcc_zero, c.mcc as mcc_one
	from uniquetimes as a
	left join zero as b
	on a.&time.=b.&time. and a.replicate=b.replicate
	left join one as c
	on a.&time.=c.&time. and a.replicate=c.replicate; quit;

*This code makes missing values of MCC (to be expected, an event likely doesn't occur at every unique day of follow-up)
retain the most recent value of the MCC. This will make the plateaus in the step function*;
Data mcc_boot;
	set mcc_boot;
	by replicate;
	retain _mcc0 _mcc1;
	if not missing(mcc_zero) then _mcc0=mcc_zero;
		else mcc_zero=_mcc0;
	drop _mcc0;
	if mcc_zero=. then mcc_zero=lag(mcc_zero);

	if not missing(mcc_one) then _mcc1=mcc_one;
		else mcc_one=_mcc1;
	drop _mcc1;
	if mcc_one=. then mcc_one=lag(mcc_one); Run;
Data mcc_boot;
	set mcc_boot;
	MCCD=mcc_one-mcc_zero;
	MCCR=mcc_one/mcc_zero; Run;
Data mcc_boot;
	set mcc_boot;
	if MCCR=. then MCCR=1.00000; Run;
Proc Univariate data = mcc_boot;
	 var mcc_one mcc_zero MCCD MCCR;
	 by time;
	 output out=norm_out 
	STDDEV= one zero diff ratio; run;
Proc sql;
	create table mcc_final_output as
	select a.time, a.mcc_zero as MCC_UNEXP,
	a.mcc_zero-1.96*b.zero as MCC_UNEXP_LCL,
	a.mcc_zero+1.96*b.zero as MCC_UNEXP_UCL,
	a.mcc_one as MCC_EXP,
	a.mcc_one-1.96*b.one as MCC_EXPOS_LCL,
	a.mcc_one+1.96*b.one as MCC_EXPOS_UCL,
	a.MCCD,
	a.MCCD-1.96*b.diff as MCCD_LCL,
	a.MCCD+1.96*b.diff as MCCD_UCL,
	a.MCCR,
	a.MCCR-1.96*b.ratio as MCCR_LCL,
	a.MCCR+1.96*b.ratio as MCCR_UCL
	from Mcc_point as a
	left join
	norm_out as b
	on  a.time=b.time; quit;
Proc datasets library=work;
	delete first mccfinal mcctemp1 mcctemp2 mcctemp3 mcc_boot norm_out one originalpats sumwtpat uniquetimes zero; Run;
%mend;

*Example call of macro*;
%MCCWEIGHTBOOT (dataname=mcc.user_friendly, bootnum=200, id=ID, status=Y, time=time, trt=A, wt=siptw, endfollowup=365);

***Plot 1: Mean cumulative count************ Example shown on the right*******;
ODS GRAPHICS on/  ANTIALIASMAX=410500 RESET IMAGENAME = "mcc_user_friendly" IMAGEFMT =PNG border=off
HEIGHT = 5in WIDTH = 5in ; ods listing image_dpi=600;
ODS LISTING GPATH = "/local/MCC 2021" ; *change your path as appropriate*;
proc sgplot data=Mcc_final_output noautolegend noborder;
	step x=time y=MCC_UNEXP/ legendlabel="Unexposed" name="d1" lineattrs=(color=red pattern=1);
	band x=time upper=MCC_UNEXP_UCL lower=MCC_UNEXP_LCL/fillattrs=(color=lightred) TRANSPARENCY=0.80;
	step x=time y=MCC_EXP/ legendlabel="Exposed" name="d2" lineattrs=(color=blue pattern=1);
	band x=time upper=MCC_EXPOS_UCL lower=MCC_EXPOS_LCL/fillattrs=(color=blue) TRANSPARENCY=0.80;
	keylegend "d1" "d2"/across=1 down=2 location=inside noborder position=topleft valueattrs=(size=10pt);
	xaxis label="Days since time origin" max=365 OFFSETMAX=0 values= (0 to 365 by 73);
	yaxis label="Mean cumulative count" OFFSETMIN=0 max=0.30 values= (0 to 10 by 1); run;




***Plot 2: Mean cumulative count difference************ Example shown on the right*******;
ODS GRAPHICS on/  ANTIALIASMAX=410500 RESET IMAGENAME = "mcc_diff_userfriendly" IMAGEFMT =PNG border=off
HEIGHT = 5in WIDTH = 5in ; ods listing image_dpi=400;
ODS LISTING GPATH = "/local/MCC 2021" ; *change your path as appropriate*;
proc sgplot data=Mcc_final_output noautolegend noborder;
	step x=time y=MCCD/ legendlabel="Mean cumulative count difference" name="d1" lineattrs=(color=green pattern=1);
	band x=time upper=MCCD_UCL lower=MCCD_LCL/fillattrs=(color=lightgreen) TRANSPARENCY=0.80;
	xaxis label="Days since time origin" max=365 OFFSETMAX=0 values= (0 to 365 by 73);
	yaxis label="Mean Cumulative Count Difference" OFFSETMIN=0 min=-3 max=3 ;
	refline 0 / axis=y label=('Null'); run;
