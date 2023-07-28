### para
rephaseint: 80(40-640)
    =rephaseinit

ccanr_gap_inc: 1024(1024-8192)

phaseprob1: 100(50-200)
phaseprob2: 300(200-500)
phaseprob3: 300(200-500)
phaseprob4: 50(0-150)
phaseprob5: 25(0-100)
phaseprob6: 25(0-100)
phaseprob7: 150(50-250)

sum(phaseprob)=950



### run
./kissat $instance --ccanr=1 --rephaseint=80 --rephaseinit=80 --ccanr_gap_inc=1024 --phaseprob1=100



--ccanr=1 fix